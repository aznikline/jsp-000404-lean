import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  rcases m.htr 2 3 4 (by decide) (by decide) with h4132 | h4132
  · rcases m.htr 2 3 5 (by decide) (by decide) with h4133 | h4133
    · rcases m.htr 2 4 5 (by decide) (by decide) with h4134 | h4134
      · rcases m.htr 3 4 5 (by decide) (by decide) with h4135 | h4135
        · rcases h1bigk with h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            rcases p4136_3 (m.d 0 1) (by simp) with h4138 | h4138
            · rcases p4136_3 (m.d 1 2) (by simp) with h4139 | h4139
              · linarith only [h4139, hlam, p4136_0]
              · rcases p4136_3 (m.d 1 3) (by simp) with h4141 | h4141
                · linarith only [h1, h4141, hlam]
                · linarith only [h10, h4141, hlam]
            · linarith only [h4138, hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [h4129, h4135, hc01, hc45, hlam, hphi, ht0b, ht5b, p4136_1]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            rcases p4136_3 (m.d 0 1) (by simp) with h4146 | h4146
            · rcases p4136_3 (m.d 1 2) (by simp) with h4147 | h4147
              · linarith only [h0, h4147, hlam]
              · rcases p4136_3 (m.d 1 3) (by simp) with h4149 | h4149
                · linarith only [h1, h4149, hlam]
                · linarith only [h4129, h4149, hlam]
            · linarith only [h4146, hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            rcases p4136_3 (m.d 0 1) (by simp) with h4153 | h4153
            · rcases p4136_3 (m.d 1 2) (by simp) with h4154 | h4154
              · linarith only [h0, h4154, hlam]
              · rcases p4136_3 (m.d 1 3) (by simp) with h4156 | h4156
                · linarith only [h1, h4156, hlam]
                · linarith only [h4130, h4156, hlam]
            · linarith only [h4153, hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [h0, hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [h10, hlam, p4136_1]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [h3576, hlam, p4136_1]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [h4058, hlam, p4136_1]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [h1, hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            rcases p4136_3 (m.d 0 1) (by simp) with h4166 | h4166
            · rcases p4136_3 (m.d 1 2) (by simp) with h4167 | h4167
              · linarith only [h10, h4167, hlam]
              · rcases p4136_3 (m.d 1 3) (by simp) with h4169 | h4169
                · rcases p4136_3 (m.d 1 4) (by simp) with h4170 | h4170
                  · linarith only [h4129, h4170, hlam]
                  · linarith only [h3576, h4170, hlam]
                · linarith only [h10, h4169, hlam]
            · linarith only [h0, h4166, hlam]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [h0, h10, h4, h4129, h4135, hc01, hc45, hlam, hphi, ht0b, ht5b, p4136_1]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            rcases p4136_3 (m.d 0 1) (by simp) with h4177 | h4177
            · rcases p4136_3 (m.d 1 2) (by simp) with h4178 | h4178
              · linarith only [h10, h4178, hlam]
              · rcases p4136_3 (m.d 1 3) (by simp) with h4180 | h4180
                · rcases p4136_3 (m.d 1 4) (by simp) with h4181 | h4181
                  · linarith only [h4129, h4181, hlam]
                  · linarith only [h4131, h4181, hlam]
                · linarith only [h4130, h4180, hlam]
            · linarith only [h3, h4177, hlam]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [h2, hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            rcases p4136_3 (m.d 0 1) (by simp) with h4187 | h4187
            · rcases p4136_3 (m.d 1 2) (by simp) with h4188 | h4188
              · linarith only [h3576, h4188, hlam]
              · rcases p4136_3 (m.d 1 3) (by simp) with h4190 | h4190
                · rcases p4136_3 (m.d 1 4) (by simp) with h4191 | h4191
                  · rcases p4136_3 (m.d 1 5) (by simp) with h4192 | h4192
                    · linarith only [h4131, h4192, hlam]
                    · linarith only [h4058, h4192, hlam]
                  · linarith only [h3576, h4191, hlam]
                · linarith only [h10, h4190, hlam]
            · linarith only [h0, h4187, hlam]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [h4129, hlam, p4136_1]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            rcases p4136_3 (m.d 0 1) (by simp) with h4200 | h4200
            · rcases p4136_3 (m.d 1 2) (by simp) with h4201 | h4201
              · linarith only [h3576, h4201, hlam]
              · rcases p4136_3 (m.d 1 3) (by simp) with h4203 | h4203
                · rcases p4136_3 (m.d 1 4) (by simp) with h4204 | h4204
                  · rcases p4136_3 (m.d 1 5) (by simp) with h4205 | h4205
                    · linarith only [h4131, h4205, hlam]
                    · rcases h1emax with h4207 | h4207 | h4207 | h4207 | h4207
                      · linarith only [h0, h3576, h4, h4132, h4207, hc15, hlam, hphi, ht01, ht0b, ht5b, p4136_1]
                      · rcases h2bigk with h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c | h4209c
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h3576, h4, h4058, h4132, hlam, p4136_1, p4209_2]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h0, h3576, h4058, h4132, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4209_1]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h0, h3576, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4209_1]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          rcases p4209_3 (m.d 0 2) (by simp) with h4214 | h4214
                          · rcases p4209_3 (m.d 1 2) (by simp) with h4215 | h4215
                            · linarith only [h0, h4215, hlam]
                            · rcases p4209_3 (m.d 2 3) (by simp) with h4217 | h4217
                              · linarith only [h4, h4217, hlam]
                              · linarith only [h4133, h4217, hlam]
                          · linarith only [h4214, hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h0, hlam, p4209_1]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h10, hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h3576, hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h4058, hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h4, hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          rcases p4209_3 (m.d 0 2) (by simp) with h4227 | h4227
                          · rcases p4209_3 (m.d 1 2) (by simp) with h4228 | h4228
                            · linarith only [h4228, hlam, p4209_0]
                            · rcases p4209_3 (m.d 2 3) (by simp) with h4230 | h4230
                              · rcases p4209_3 (m.d 2 4) (by simp) with h4231 | h4231
                                · linarith only [h4132, h4231, hlam]
                                · linarith only [h3576, h4231, hlam]
                              · linarith only [h4230, hlam, p4209_0]
                          · linarith only [h0, h4227, hlam]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h3576, h4058, hc12, hc23, hlam, hphi, p4136_1, p4209_1]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4209_1]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h5, hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          rcases p4209_3 (m.d 0 2) (by simp) with h4240 | h4240
                          · rcases p4209_3 (m.d 1 2) (by simp) with h4241 | h4241
                            · linarith only [h4241, hlam, p4209_0]
                            · rcases p4209_3 (m.d 2 3) (by simp) with h4243 | h4243
                              · rcases p4209_3 (m.d 2 4) (by simp) with h4244 | h4244
                                · rcases p4209_3 (m.d 2 5) (by simp) with h4245 | h4245
                                  · linarith only [h4134, h4245, hlam]
                                  · linarith only [h4058, h4245, hlam]
                                · linarith only [h4244, hlam, p4209_0]
                              · linarith only [h10, h4243, hlam]
                          · linarith only [h0, h4240, hlam]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h4132, hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h4058, hc12, hc24, hlam, hphi, p4209_1]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h6, hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          rcases p4209_3 (m.d 0 2) (by simp) with h4255 | h4255
                          · rcases p4209_3 (m.d 1 2) (by simp) with h4256 | h4256
                            · linarith only [h4256, hlam, p4209_0]
                            · rcases p4209_3 (m.d 2 3) (by simp) with h4258 | h4258
                              · rcases p4209_3 (m.d 2 4) (by simp) with h4259 | h4259
                                · rcases p4209_3 (m.d 2 5) (by simp) with h4260 | h4260
                                  · rcases h4bigk with h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c | h4261c
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h0, h4, h4058, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4261_1]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h0, h3576, h4, h4058, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4261_1]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      rcases p4261_3 (m.d 0 4) (by simp) with h4265 | h4265
                                      · rcases p4261_3 (m.d 1 4) (by simp) with h4266 | h4266
                                        · linarith only [h2, h4266, hlam]
                                        · linarith only [h4129, h4266, hlam]
                                      · linarith only [h4265, h7, hlam]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      rcases p4261_3 (m.d 0 4) (by simp) with h4270 | h4270
                                      · rcases p4261_3 (m.d 1 4) (by simp) with h4271 | h4271
                                        · linarith only [h2, h4271, hlam]
                                        · linarith only [h4131, h4271, hlam]
                                      · linarith only [h4270, hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h2, hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h3576, hlam, p4261_1]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h2, h4135, hc01, hc45, hlam, hphi, ht0b, ht5b, p4261_1]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      rcases p4261_3 (m.d 0 4) (by simp) with h4279 | h4279
                                      · rcases p4261_3 (m.d 1 4) (by simp) with h4280 | h4280
                                        · rcases p4261_3 (m.d 2 4) (by simp) with h4281 | h4281
                                          · rcases p4261_3 (m.d 3 4) (by simp) with h4282 | h4282
                                            · linarith only [h4129, h4282, hlam]
                                            · linarith only [h4135, h4282, hlam]
                                          · linarith only [h4134, h4281, hlam]
                                        · linarith only [h4280, hlam, p4261_0]
                                      · linarith only [h4279, h9, hlam]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h5, hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h0, h4, h4129, h4132, h4135, hc01, hc45, hlam, hphi, ht0b, ht5b, p4261_1]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h0, h4, h4132, h4135, hc01, hc45, hlam, hphi, ht0b, ht5b, p4261_1]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      rcases p4261_3 (m.d 0 4) (by simp) with h4292 | h4292
                                      · rcases p4261_3 (m.d 1 4) (by simp) with h4293 | h4293
                                        · linarith only [h3576, h4293, hlam]
                                        · linarith only [h4131, h4293, hlam]
                                      · linarith only [h4292, h9, hlam]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h7, hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h4129, hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h4132, hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h0, h10, h4, h4129, hc01, hc45, hlam, hphi, ht0b, ht5b, p4261_1]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h9, hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h4131, hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h4134, hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [h4135, hlam, p4261_0]
                                    · have p4261_0 := h4261c.1
                                      have p4261_1 := h4261c.2.1
                                      have p4261_2 := h4261c.2.2.1
                                      have p4261_3 := h4261c.2.2.2
                                      linarith only [hlam, p4261_0]
                                  · linarith only [h4260, hlam, p4209_0]
                                · linarith only [h3576, h4259, hlam]
                              · linarith only [h10, h4258, hlam]
                          · linarith only [h0, h4255, hlam]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h4133, hlam, p4209_0]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [h4134, hlam, p4209_1]
                        · have p4209_0 := h4209c.1
                          have p4209_1 := h4209c.2.1
                          have p4209_2 := h4209c.2.2.1
                          have p4209_3 := h4209c.2.2.2
                          linarith only [hlam, p4209_0]
                      · linarith only [h4058, h4129, h4207, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1]
                      · linarith only [h4058, h4207, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1]
                      · rcases h2bigk with h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h10, h4, h4058, h4129, hlam, p4136_1, p4316_2]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h10, h4058, h4129, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4316_1]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h0, h3576, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4316_1]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          rcases p4316_3 (m.d 0 2) (by simp) with h4321 | h4321
                          · rcases p4316_3 (m.d 1 2) (by simp) with h4322 | h4322
                            · linarith only [h0, h4322, hlam]
                            · rcases p4316_3 (m.d 2 3) (by simp) with h4324 | h4324
                              · linarith only [h4, h4324, hlam]
                              · linarith only [h4133, h4324, hlam]
                          · linarith only [h4321, hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h0, hlam, p4316_1]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h10, hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h3576, hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h4058, hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h4, hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          rcases p4316_3 (m.d 0 2) (by simp) with h4334 | h4334
                          · rcases p4316_3 (m.d 1 2) (by simp) with h4335 | h4335
                            · linarith only [h4335, hlam, p4316_0]
                            · rcases p4316_3 (m.d 2 3) (by simp) with h4337 | h4337
                              · rcases p4316_3 (m.d 2 4) (by simp) with h4338 | h4338
                                · linarith only [h4132, h4338, hlam]
                                · linarith only [h3576, h4338, hlam]
                              · linarith only [h4337, hlam, p4316_0]
                          · linarith only [h0, h4334, hlam]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h3576, h4058, hc12, hc23, hlam, hphi, p4136_1, p4316_1]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4316_1]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h5, hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          rcases p4316_3 (m.d 0 2) (by simp) with h4347 | h4347
                          · rcases p4316_3 (m.d 1 2) (by simp) with h4348 | h4348
                            · linarith only [h4348, hlam, p4316_0]
                            · rcases p4316_3 (m.d 2 3) (by simp) with h4350 | h4350
                              · rcases p4316_3 (m.d 2 4) (by simp) with h4351 | h4351
                                · rcases p4316_3 (m.d 2 5) (by simp) with h4352 | h4352
                                  · linarith only [h4134, h4352, hlam]
                                  · linarith only [h4058, h4352, hlam]
                                · linarith only [h4351, hlam, p4316_0]
                              · linarith only [h10, h4350, hlam]
                          · linarith only [h0, h4347, hlam]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h4132, hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h4058, hc12, hc24, hlam, hphi, p4316_1]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h6, hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          rcases p4316_3 (m.d 0 2) (by simp) with h4362 | h4362
                          · rcases p4316_3 (m.d 1 2) (by simp) with h4363 | h4363
                            · linarith only [h4363, hlam, p4316_0]
                            · rcases p4316_3 (m.d 2 3) (by simp) with h4365 | h4365
                              · rcases p4316_3 (m.d 2 4) (by simp) with h4366 | h4366
                                · rcases p4316_3 (m.d 2 5) (by simp) with h4367 | h4367
                                  · rcases h4bigk with h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h4058, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4368_1]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h0, h3576, h4, h4058, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4368_1]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      rcases p4368_3 (m.d 0 4) (by simp) with h4372 | h4372
                                      · rcases p4368_3 (m.d 1 4) (by simp) with h4373 | h4373
                                        · linarith only [h2, h4373, hlam]
                                        · linarith only [h4129, h4373, hlam]
                                      · linarith only [h4372, h7, hlam]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      rcases p4368_3 (m.d 0 4) (by simp) with h4377 | h4377
                                      · rcases p4368_3 (m.d 1 4) (by simp) with h4378 | h4378
                                        · linarith only [h2, h4378, hlam]
                                        · linarith only [h4131, h4378, hlam]
                                      · linarith only [h4377, hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h2, hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h3576, hlam, p4368_1]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h1, h4129, h4135, hc01, hc45, hlam, hphi, ht0b, ht5b, p4368_1]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      rcases p4368_3 (m.d 0 4) (by simp) with h4386 | h4386
                                      · rcases p4368_3 (m.d 1 4) (by simp) with h4387 | h4387
                                        · rcases p4368_3 (m.d 2 4) (by simp) with h4388 | h4388
                                          · rcases p4368_3 (m.d 3 4) (by simp) with h4389 | h4389
                                            · linarith only [h4129, h4389, hlam]
                                            · linarith only [h4135, h4389, hlam]
                                          · linarith only [h4134, h4388, hlam]
                                        · linarith only [h4387, hlam, p4368_0]
                                      · linarith only [h4386, h9, hlam]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h5, hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h0, h4, h4058, h4132, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4368_1]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h0, h4, h4132, h4135, hc01, hc45, hlam, hphi, ht0b, ht5b, p4368_1]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      rcases p4368_3 (m.d 0 4) (by simp) with h4399 | h4399
                                      · rcases p4368_3 (m.d 1 4) (by simp) with h4400 | h4400
                                        · linarith only [h3576, h4400, hlam]
                                        · linarith only [h4131, h4400, hlam]
                                      · linarith only [h4399, h9, hlam]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h7, hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h4129, hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h4132, hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h0, h10, h4, h4129, hc01, hc45, hlam, hphi, ht0b, ht5b, p4368_1]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h9, hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h4131, hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h4134, hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [h4135, hlam, p4368_0]
                                    · have p4368_0 := h4368c.1
                                      have p4368_1 := h4368c.2.1
                                      have p4368_2 := h4368c.2.2.1
                                      have p4368_3 := h4368c.2.2.2
                                      linarith only [hlam, p4368_0]
                                  · linarith only [h4367, hlam, p4316_0]
                                · linarith only [h3576, h4366, hlam]
                              · linarith only [h10, h4365, hlam]
                          · linarith only [h0, h4362, hlam]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h4133, hlam, p4316_0]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [h4134, hlam, p4316_1]
                        · have p4316_0 := h4316c.1
                          have p4316_1 := h4316c.2.1
                          have p4316_2 := h4316c.2.2.1
                          have p4316_3 := h4316c.2.2.2
                          linarith only [hlam, p4316_0]
                  · linarith only [h4131, h4204, hlam]
                · linarith only [h4130, h4203, hlam]
            · linarith only [h3, h4200, hlam]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [h3, hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            rcases p4136_3 (m.d 0 1) (by simp) with h4425 | h4425
            · rcases p4136_3 (m.d 1 2) (by simp) with h4426 | h4426
              · linarith only [h4058, h4426, hlam]
              · rcases p4136_3 (m.d 1 3) (by simp) with h4428 | h4428
                · rcases p4136_3 (m.d 1 4) (by simp) with h4429 | h4429
                  · rcases p4136_3 (m.d 1 5) (by simp) with h4430 | h4430
                    · rcases h1emax with h4431 | h4431 | h4431 | h4431 | h4431
                      · linarith only [h0, h10, h4, h4129, h4431, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h2bigk with h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c | h4433c
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [hlam, p4433_0]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h10, h4, h4129, h4131, hlam, p4136_1, p4433_2]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h0, h10, h4129, h4131, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4433_1]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h0, h3576, h4131, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4433_1]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h0, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4433_1]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h0, hlam, p4433_1]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [hlam, p4433_0]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h10, hlam, p4433_0]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h3576, hlam, p4433_0]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h4058, hlam, p4433_0]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h4, hlam, p4433_0]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          rcases p4433_3 (m.d 0 2) (by simp) with h4445 | h4445
                          · rcases p4433_3 (m.d 1 2) (by simp) with h4446 | h4446
                            · linarith only [h4446, hlam, p4433_0]
                            · rcases p4433_3 (m.d 2 3) (by simp) with h4448 | h4448
                              · rcases p4433_3 (m.d 2 4) (by simp) with h4449 | h4449
                                · linarith only [h4132, h4449, hlam]
                                · linarith only [h3576, h4449, hlam]
                              · linarith only [h4448, hlam, p4433_0]
                          · linarith only [h0, h4445, hlam]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [hlam, p4433_0]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h3576, h4131, hc12, hc23, hlam, hphi, p4136_1, p4433_1]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4433_1]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h5, hlam, p4433_0]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          rcases p4433_3 (m.d 0 2) (by simp) with h4458 | h4458
                          · rcases p4433_3 (m.d 1 2) (by simp) with h4459 | h4459
                            · linarith only [h4459, hlam, p4433_0]
                            · rcases p4433_3 (m.d 2 3) (by simp) with h4461 | h4461
                              · rcases p4433_3 (m.d 2 4) (by simp) with h4462 | h4462
                                · rcases p4433_3 (m.d 2 5) (by simp) with h4463 | h4463
                                  · linarith only [h4134, h4463, hlam]
                                  · linarith only [h4058, h4463, hlam]
                                · linarith only [h4462, hlam, p4433_0]
                              · linarith only [h10, h4461, hlam]
                          · linarith only [h0, h4458, hlam]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h4132, hlam, p4433_0]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [hlam, p4433_0]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h4058, hc12, hc24, hlam, hphi, p4136_1, p4433_1]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h6, hlam, p4433_0]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          rcases p4433_3 (m.d 0 2) (by simp) with h4473 | h4473
                          · rcases p4433_3 (m.d 1 2) (by simp) with h4474 | h4474
                            · linarith only [h4474, hlam, p4433_0]
                            · rcases p4433_3 (m.d 2 3) (by simp) with h4476 | h4476
                              · rcases p4433_3 (m.d 2 4) (by simp) with h4477 | h4477
                                · rcases p4433_3 (m.d 2 5) (by simp) with h4478 | h4478
                                  · rcases h4bigk with h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h4131, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4479_1]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h0, h3576, h4, h4131, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4136_1, p4479_1]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      rcases p4479_3 (m.d 0 4) (by simp) with h4483 | h4483
                                      · rcases p4479_3 (m.d 1 4) (by simp) with h4484 | h4484
                                        · linarith only [h2, h4484, hlam]
                                        · linarith only [h4129, h4484, hlam]
                                      · linarith only [h4483, h7, hlam]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      rcases p4479_3 (m.d 0 4) (by simp) with h4488 | h4488
                                      · rcases p4479_3 (m.d 1 4) (by simp) with h4489 | h4489
                                        · linarith only [h2, h4489, hlam]
                                        · linarith only [h4131, h4489, hlam]
                                      · linarith only [h4488, hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h2, hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h3576, hlam, p4479_1]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h1, h4129, h4135, hc01, hc45, hlam, hphi, ht0b, ht5b, p4479_1]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      rcases p4479_3 (m.d 0 4) (by simp) with h4497 | h4497
                                      · rcases p4479_3 (m.d 1 4) (by simp) with h4498 | h4498
                                        · rcases p4479_3 (m.d 2 4) (by simp) with h4499 | h4499
                                          · rcases p4479_3 (m.d 3 4) (by simp) with h4500 | h4500
                                            · linarith only [h4129, h4500, hlam]
                                            · linarith only [h4135, h4500, hlam]
                                          · linarith only [h4134, h4499, hlam]
                                        · linarith only [h4498, hlam, p4479_0]
                                      · linarith only [h4497, h9, hlam]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h5, hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h0, h4, h4129, h4132, h4135, hc01, hc45, hlam, hphi, ht0b, ht5b, p4479_1]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h0, h4, h4132, h4135, hc01, hc45, hlam, hphi, ht0b, ht5b, p4479_1]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      rcases p4479_3 (m.d 0 4) (by simp) with h4510 | h4510
                                      · rcases p4479_3 (m.d 1 4) (by simp) with h4511 | h4511
                                        · linarith only [h3576, h4511, hlam]
                                        · linarith only [h4131, h4511, hlam]
                                      · linarith only [h4510, h9, hlam]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h7, hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h4129, hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h4132, hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h0, h10, h4, h4129, hc01, hc45, hlam, hphi, ht0b, ht5b, p4479_1]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h9, hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h4131, hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h4134, hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [h4135, hlam, p4479_0]
                                    · have p4479_0 := h4479c.1
                                      have p4479_1 := h4479c.2.1
                                      have p4479_2 := h4479c.2.2.1
                                      have p4479_3 := h4479c.2.2.2
                                      linarith only [hlam, p4479_0]
                                  · linarith only [h4478, hlam, p4433_0]
                                · linarith only [h3576, h4477, hlam]
                              · linarith only [h10, h4476, hlam]
                          · linarith only [h0, h4473, hlam]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h4133, hlam, p4433_0]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [h4134, hlam, p4433_1]
                        · have p4433_0 := h4433c.1
                          have p4433_1 := h4433c.2.1
                          have p4433_2 := h4433c.2.2.1
                          have p4433_3 := h4433c.2.2.2
                          linarith only [hlam, p4433_0]
                      · linarith only [h4129, h4131, h4431, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1]
                      · linarith only [h4131, h4431, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1]
                      · linarith only [h4431, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1]
                    · linarith only [h4058, h4430, hlam]
                  · linarith only [h3576, h4429, hlam]
                · linarith only [h10, h4428, hlam]
            · linarith only [h0, h4425, hlam]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [h4130, hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [h4131, hlam, p4136_0]
          · have p4136_0 := h4136c.1
            have p4136_1 := h4136c.2.1
            have p4136_2 := h4136c.2.2.1
            have p4136_3 := h4136c.2.2.2
            linarith only [hlam, p4136_0]
        · rcases h1bigk with h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c | h4542c
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [hlam, p4542_0]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            rcases p4542_3 (m.d 0 1) (by simp) with h4544 | h4544
            · rcases p4542_3 (m.d 1 2) (by simp) with h4545 | h4545
              · linarith only [h4545, hlam, p4542_0]
              · rcases p4542_3 (m.d 1 3) (by simp) with h4547 | h4547
                · linarith only [h1, h4547, hlam]
                · linarith only [h10, h4547, hlam]
            · linarith only [h4544, hlam, p4542_0]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h4129, h4131, h4135, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4542_1]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h4131, h4135, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4542_1]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            rcases p4542_3 (m.d 0 1) (by simp) with h4553 | h4553
            · rcases p4542_3 (m.d 1 2) (by simp) with h4554 | h4554
              · linarith only [h0, h4554, hlam]
              · rcases p4542_3 (m.d 1 3) (by simp) with h4556 | h4556
                · linarith only [h1, h4556, hlam]
                · linarith only [h4130, h4556, hlam]
            · linarith only [h4553, hlam, p4542_0]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h0, hlam, p4542_0]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [hlam, p4542_0]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h10, hlam, p4542_1]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h3576, hlam, p4542_1]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h4058, hlam, p4542_1]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h1, hlam, p4542_0]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            rcases p4542_3 (m.d 0 1) (by simp) with h4566 | h4566
            · rcases p4542_3 (m.d 1 2) (by simp) with h4567 | h4567
              · linarith only [h10, h4567, hlam]
              · rcases p4542_3 (m.d 1 3) (by simp) with h4569 | h4569
                · rcases p4542_3 (m.d 1 4) (by simp) with h4570 | h4570
                  · linarith only [h4129, h4570, hlam]
                  · linarith only [h3576, h4570, hlam]
                · linarith only [h10, h4569, hlam]
            · linarith only [h0, h4566, hlam]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [hlam, p4542_0]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h4131, h4135, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4542_1]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h0, h10, h4, h4131, h4135, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4542_1]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h2, hlam, p4542_0]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            rcases p4542_3 (m.d 0 1) (by simp) with h4579 | h4579
            · rcases p4542_3 (m.d 1 2) (by simp) with h4580 | h4580
              · linarith only [h3576, h4580, hlam]
              · rcases p4542_3 (m.d 1 3) (by simp) with h4582 | h4582
                · rcases p4542_3 (m.d 1 4) (by simp) with h4583 | h4583
                  · rcases p4542_3 (m.d 1 5) (by simp) with h4584 | h4584
                    · linarith only [h4131, h4584, hlam]
                    · linarith only [h4058, h4584, hlam]
                  · linarith only [h3576, h4583, hlam]
                · linarith only [h10, h4582, hlam]
            · linarith only [h0, h4579, hlam]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h4129, hlam, p4542_1]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [hlam, p4542_0]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h2, h4131, h4135, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4542_1]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h3, hlam, p4542_0]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            rcases p4542_3 (m.d 0 1) (by simp) with h4594 | h4594
            · rcases p4542_3 (m.d 1 2) (by simp) with h4595 | h4595
              · linarith only [h4058, h4595, hlam]
              · rcases p4542_3 (m.d 1 3) (by simp) with h4597 | h4597
                · rcases p4542_3 (m.d 1 4) (by simp) with h4598 | h4598
                  · rcases p4542_3 (m.d 1 5) (by simp) with h4599 | h4599
                    · rcases h1emax with h4600 | h4600 | h4600 | h4600 | h4600
                      · linarith only [h3, h4600, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4542_1]
                      · rcases h2bigk with h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c | h4602c
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [hlam, p4602_0]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h4, h4058, h4132, h4134, hlam, p4542_1, p4602_2]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h0, h4058, h4132, h4134, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4542_1, p4602_1]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h0, h4058, h4134, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4542_1, p4602_1]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h0, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4542_1, p4602_1]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h0, hlam, p4602_1]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [hlam, p4602_0]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h10, hlam, p4602_0]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h3576, hlam, p4602_0]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h4058, hlam, p4602_0]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h4, hlam, p4602_0]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          rcases p4602_3 (m.d 0 2) (by simp) with h4614 | h4614
                          · rcases p4602_3 (m.d 1 2) (by simp) with h4615 | h4615
                            · linarith only [h4615, hlam, p4602_0]
                            · rcases p4602_3 (m.d 2 3) (by simp) with h4617 | h4617
                              · rcases p4602_3 (m.d 2 4) (by simp) with h4618 | h4618
                                · linarith only [h4132, h4618, hlam]
                                · linarith only [h3576, h4618, hlam]
                              · linarith only [h4617, hlam, p4602_0]
                          · linarith only [h0, h4614, hlam]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [hlam, p4602_0]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h4, h4058, h4134, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4542_1, p4602_1]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4542_1, p4602_1]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h5, hlam, p4602_0]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          rcases p4602_3 (m.d 0 2) (by simp) with h4627 | h4627
                          · rcases p4602_3 (m.d 1 2) (by simp) with h4628 | h4628
                            · linarith only [h4628, hlam, p4602_0]
                            · rcases p4602_3 (m.d 2 3) (by simp) with h4630 | h4630
                              · rcases p4602_3 (m.d 2 4) (by simp) with h4631 | h4631
                                · rcases p4602_3 (m.d 2 5) (by simp) with h4632 | h4632
                                  · linarith only [h4134, h4632, hlam]
                                  · linarith only [h4058, h4632, hlam]
                                · linarith only [h4631, hlam, p4602_0]
                              · linarith only [h10, h4630, hlam]
                          · linarith only [h0, h4627, hlam]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h4132, hlam, p4602_0]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [hlam, p4602_0]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h4058, h5, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4542_1, p4602_1]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h6, hlam, p4602_0]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          rcases p4602_3 (m.d 0 2) (by simp) with h4642 | h4642
                          · rcases p4602_3 (m.d 1 2) (by simp) with h4643 | h4643
                            · linarith only [h4643, hlam, p4602_0]
                            · rcases p4602_3 (m.d 2 3) (by simp) with h4645 | h4645
                              · rcases p4602_3 (m.d 2 4) (by simp) with h4646 | h4646
                                · rcases p4602_3 (m.d 2 5) (by simp) with h4647 | h4647
                                  · rcases h4bigk with h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h0, h4, h4131, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4542_1, p4648_1]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h0, h3576, h4, h4131, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4542_1, p4648_1]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      rcases p4648_3 (m.d 0 4) (by simp) with h4652 | h4652
                                      · rcases p4648_3 (m.d 1 4) (by simp) with h4653 | h4653
                                        · linarith only [h2, h4653, hlam]
                                        · linarith only [h4129, h4653, hlam]
                                      · linarith only [h4652, h7, hlam]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      rcases p4648_3 (m.d 0 4) (by simp) with h4657 | h4657
                                      · rcases p4648_3 (m.d 1 4) (by simp) with h4658 | h4658
                                        · linarith only [h2, h4658, hlam]
                                        · linarith only [h4131, h4658, hlam]
                                      · linarith only [h4657, hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h2, hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h3576, hlam, p4648_1]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      rcases p4648_3 (m.d 0 4) (by simp) with h4665 | h4665
                                      · rcases p4648_3 (m.d 1 4) (by simp) with h4666 | h4666
                                        · rcases p4648_3 (m.d 2 4) (by simp) with h4667 | h4667
                                          · rcases p4648_3 (m.d 3 4) (by simp) with h4668 | h4668
                                            · linarith only [h4129, h4668, hlam]
                                            · rcases p4648_3 (m.d 4 5) (by simp) with h4670 | h4670
                                              · linarith only [h4131, h4670, hlam]
                                              · linarith only [h4135, h4670, hlam]
                                          · linarith only [h4132, h4667, hlam]
                                        · linarith only [h4129, h4666, hlam]
                                      · linarith only [h4665, h7, hlam]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h1, h4129, h4135, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4648_1]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h5, hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h0, h4131, h4135, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4648_1]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      rcases p4648_3 (m.d 0 4) (by simp) with h4680 | h4680
                                      · rcases p4648_3 (m.d 1 4) (by simp) with h4681 | h4681
                                        · linarith only [h3576, h4681, hlam]
                                        · linarith only [h4129, h4681, hlam]
                                      · linarith only [h4680, h7, hlam]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h0, h4, h4132, h4135, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4648_1]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h7, hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h4129, hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h4132, hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h4135, hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h9, hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h4131, hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h4134, hlam, p4648_0]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [h1, h4129, h4131, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4648_1]
                                    · have p4648_0 := h4648c.1
                                      have p4648_1 := h4648c.2.1
                                      have p4648_2 := h4648c.2.2.1
                                      have p4648_3 := h4648c.2.2.2
                                      linarith only [hlam, p4648_0]
                                  · linarith only [h4647, hlam, p4602_0]
                                · linarith only [h3576, h4646, hlam]
                              · linarith only [h10, h4645, hlam]
                          · linarith only [h0, h4642, hlam]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h4133, hlam, p4602_0]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [h4134, hlam, p4602_1]
                        · have p4602_0 := h4602c.1
                          have p4602_1 := h4602c.2.1
                          have p4602_2 := h4602c.2.2.1
                          have p4602_3 := h4602c.2.2.2
                          linarith only [hlam, p4602_0]
                      · linarith only [h4130, h4600, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4542_1]
                      · linarith only [h4131, h4600, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4542_1]
                      · linarith only [h4600, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4542_1]
                    · linarith only [h4058, h4599, hlam]
                  · linarith only [h3576, h4598, hlam]
                · linarith only [h10, h4597, hlam]
            · linarith only [h0, h4594, hlam]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h4130, hlam, p4542_0]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [h4131, hlam, p4542_0]
          · have p4542_0 := h4542c.1
            have p4542_1 := h4542c.2.1
            have p4542_2 := h4542c.2.2.1
            have p4542_3 := h4542c.2.2.2
            linarith only [hlam, p4542_0]
      · linarith only [h1, h3576, h4129, h4131, h4134, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · linarith only [h10, h4130, h4133, hlam]
  · linarith only [h10, h4129, h4132, hlam]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  linarith only [h1, h4129, h4131, h4719, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 0 1) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 1) ∧ (m.d 0 1) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 0 1) ≤ z)))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [hlam, p4721_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 0 1) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 0 1) ∧ (m.d 1 2) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 2) ≤ z)))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h0, h3576, h4, h4131, h4716, h4718, hlam, p4721_2]

end R2N4
