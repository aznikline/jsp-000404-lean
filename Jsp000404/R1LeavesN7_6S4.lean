import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1799 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1923 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4008 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  have h1799 := hg1799
  rcases m.htr 0 4 5 (by decide) (by decide) with h4130 | h4130
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4131 | h4131
    · linarith only [h0, h4, h4131, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4133 | h4133
      · linarith only [h0, h1270, h4133, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4135 | h4135
        · linarith only [h0, h1799, h4135, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4137 | h4137
          · linarith only [h1, h1923, h4137, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4139 | h4139
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4140 | h4140
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4141 | h4141
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4142 | h4142
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4143 | h4143
                    · rcases h0bigk with h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c | h4144c
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [hlam, p4144_0]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        rcases p4144_3 (m.d 0 1) (by simp) with h4146 | h4146
                        · rcases p4144_3 (m.d 0 2) (by simp) with h4147 | h4147
                          · linarith only [h0, h4147, hlam]
                          · rcases p4144_3 (m.d 0 3) (by simp) with h4149 | h4149
                            · linarith only [h1, h4149, hlam]
                            · linarith only [h4, h4149, hlam]
                        · linarith only [h0, h4146, hlam]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        rcases p4144_3 (m.d 0 1) (by simp) with h4153 | h4153
                        · rcases p4144_3 (m.d 0 2) (by simp) with h4154 | h4154
                          · linarith only [h0, h4154, hlam]
                          · rcases p4144_3 (m.d 0 3) (by simp) with h4156 | h4156
                            · linarith only [h1, h4156, hlam]
                            · rcases p4144_3 (m.d 0 4) (by simp) with h4158 | h4158
                              · linarith only [h2, h4158, hlam]
                              · linarith only [h1923, h4158, hlam]
                        · linarith only [h1, h4153, hlam]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h2, h4139, hc45, hlam, hphi, ht0b, ht5b, p4144_1, u0elo0]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        rcases p4144_3 (m.d 0 1) (by simp) with h4163 | h4163
                        · rcases p4144_3 (m.d 0 2) (by simp) with h4164 | h4164
                          · linarith only [h0, h4164, hlam]
                          · rcases p4144_3 (m.d 0 3) (by simp) with h4166 | h4166
                            · linarith only [h1, h4166, hlam]
                            · rcases p4144_3 (m.d 0 4) (by simp) with h4168 | h4168
                              · linarith only [h2, h4168, hlam]
                              · linarith only [h4130, h4168, hlam]
                        · linarith only [h3, h4163, hlam]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h0, hlam, p4144_0]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [hlam, p4144_0]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h4, hlam, p4144_0]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h1270, hlam, p4144_1]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h1799, hlam, p4144_0]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h1, hlam, p4144_1]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h0, h4008, h4140, h4143, hc12, hc23, hlam, hphi, p4144_1]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [hlam, p4144_0]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h1923, hlam, p4144_1]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h4008, hlam, p4144_1]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h2, hlam, p4144_0]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h0, h1923, h4140, hc12, hc23, hlam, hphi, p4144_1]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h1, h1923, h4131, h4140, hc12, hc23, hlam, hphi, p4144_1]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [hlam, p4144_0]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h1, h1923, h4008, h4131, h4140, hc12, hc23, hlam, hphi, p4144_1]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h3, hlam, p4144_0]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h0, h4008, h4140, h4143, hc12, hc23, hlam, hphi, p4144_1]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h1, h4008, h4131, h4140, h4143, hc12, hc23, hlam, hphi, p4144_1]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [h4130, hlam, p4144_1]
                      · have p4144_0 := h4144c.1
                        have p4144_1 := h4144c.2.1
                        have p4144_2 := h4144c.2.2.1
                        have p4144_3 := h4144c.2.2.2
                        linarith only [hlam, p4144_0]
                    · linarith only [h1923, h2, h4139, h4143, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1923, h2, h4139, h4140, h4142, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h1, h1923, h4131, h4140, h4141, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4195 | h4195
                · linarith only [h1, h4008, h4131, h4140, h4195, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4197 | h4197
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4198 | h4198
                    · rcases h0bigk with h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c | h4199c
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [hlam, p4199_0]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        rcases p4199_3 (m.d 0 1) (by simp) with h4201 | h4201
                        · rcases p4199_3 (m.d 0 2) (by simp) with h4202 | h4202
                          · linarith only [h0, h4202, hlam]
                          · rcases p4199_3 (m.d 0 3) (by simp) with h4204 | h4204
                            · linarith only [h1, h4204, hlam]
                            · linarith only [h4, h4204, hlam]
                        · linarith only [h0, h4201, hlam]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        rcases p4199_3 (m.d 0 1) (by simp) with h4208 | h4208
                        · rcases p4199_3 (m.d 0 2) (by simp) with h4209 | h4209
                          · linarith only [h0, h4209, hlam]
                          · rcases p4199_3 (m.d 0 3) (by simp) with h4211 | h4211
                            · linarith only [h1, h4211, hlam]
                            · rcases p4199_3 (m.d 0 4) (by simp) with h4213 | h4213
                              · linarith only [h2, h4213, hlam]
                              · linarith only [h1923, h4213, hlam]
                        · linarith only [h1, h4208, hlam]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [h2, h4139, hc45, hlam, hphi, ht0b, ht5b, p4199_1, u0elo0]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        rcases p4199_3 (m.d 0 1) (by simp) with h4218 | h4218
                        · rcases p4199_3 (m.d 0 2) (by simp) with h4219 | h4219
                          · linarith only [h0, h4219, hlam]
                          · rcases p4199_3 (m.d 0 3) (by simp) with h4221 | h4221
                            · linarith only [h1, h4221, hlam]
                            · rcases p4199_3 (m.d 0 4) (by simp) with h4223 | h4223
                              · linarith only [h2, h4223, hlam]
                              · linarith only [h4130, h4223, hlam]
                        · linarith only [h3, h4218, hlam]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [h0, hlam, p4199_0]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [hlam, p4199_0]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [h4, hlam, p4199_0]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [h1270, hlam, p4199_1]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [h1799, hlam, p4199_0]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [h1, hlam, p4199_1]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [h0, h4, h4195, h4198, hc12, hc34, hlam, hphi, ht23, p4199_1]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [hlam, p4199_0]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [h1923, hlam, p4199_1]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [h4008, hlam, p4199_1]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [h2, hlam, p4199_0]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        rcases p4199_3 (m.d 0 1) (by simp) with h4238 | h4238
                        · rcases p4199_3 (m.d 0 2) (by simp) with h4239 | h4239
                          · linarith only [h1270, h4239, hlam]
                          · rcases p4199_3 (m.d 0 3) (by simp) with h4241 | h4241
                            · linarith only [h1923, h4241, hlam]
                            · linarith only [h4, h4241, hlam]
                        · linarith only [h0, h4238, hlam]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        rcases p4199_3 (m.d 0 1) (by simp) with h4245 | h4245
                        · rcases p4199_3 (m.d 0 2) (by simp) with h4246 | h4246
                          · linarith only [h1270, h4246, hlam]
                          · rcases p4199_3 (m.d 0 3) (by simp) with h4248 | h4248
                            · linarith only [h1923, h4248, hlam]
                            · rcases p4199_3 (m.d 0 4) (by simp) with h4250 | h4250
                              · rcases p4199_3 (m.d 0 5) (by simp) with h4251 | h4251
                                · linarith only [h4130, h4251, hlam]
                                · linarith only [h4008, h4251, hlam]
                              · linarith only [h1923, h4250, hlam]
                        · linarith only [h1, h4245, hlam]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [hlam, p4199_0]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        rcases p4199_3 (m.d 0 1) (by simp) with h4257 | h4257
                        · rcases p4199_3 (m.d 0 2) (by simp) with h4258 | h4258
                          · linarith only [h1270, h4258, hlam]
                          · rcases p4199_3 (m.d 0 3) (by simp) with h4260 | h4260
                            · linarith only [h1923, h4260, hlam]
                            · rcases p4199_3 (m.d 0 4) (by simp) with h4262 | h4262
                              · rcases p4199_3 (m.d 0 5) (by simp) with h4263 | h4263
                                · linarith only [h4130, h4263, hlam]
                                · rcases h0emin with h4265 | h4265 | h4265 | h4265 | h4265
                                  · rcases h2bigk with h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c | h4266c
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h4, h4195, h4198, hc12, hc34, hlam, hphi, ht23, p4266_1]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h4, hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h1270, hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h1799, hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h0, hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h4131, hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h4133, hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h4135, hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h4195, h4198, hc02, hc34, hlam, hphi, ht23, p4266_1]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h4195, h4198, hc12, hc34, hlam, hphi, ht23, p4266_1]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h4140, hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h4195, hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      rcases p4266_3 (m.d 0 2) (by simp) with h4282 | h4282
                                      · linarith only [h4282, hlam, p4266_0]
                                      · rcases p4266_3 (m.d 1 2) (by simp) with h4284 | h4284
                                        · linarith only [h4133, h4284, hlam]
                                        · rcases p4266_3 (m.d 2 3) (by simp) with h4286 | h4286
                                          · linarith only [h4140, h4286, hlam]
                                          · linarith only [h4, h4286, hlam]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      rcases p4266_3 (m.d 0 2) (by simp) with h4289 | h4289
                                      · linarith only [h1270, h4289, hlam]
                                      · linarith only [h0, h4289, hlam]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h0, h4, hc12, hc24, hlam, hphi, p4266_1]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h0, h4, h4140, h4195, hc12, hc34, hlam, hphi, ht23, p4266_1]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      rcases p4266_3 (m.d 0 2) (by simp) with h4295 | h4295
                                      · linarith only [h4295, hlam, p4266_0]
                                      · rcases p4266_3 (m.d 1 2) (by simp) with h4297 | h4297
                                        · linarith only [h4135, h4297, hlam]
                                        · rcases p4266_3 (m.d 2 3) (by simp) with h4299 | h4299
                                          · linarith only [h4195, h4299, hlam]
                                          · linarith only [h4, h4299, hlam]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      rcases p4266_3 (m.d 0 2) (by simp) with h4302 | h4302
                                      · linarith only [h1799, h4302, hlam]
                                      · linarith only [h0, h4302, hlam]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p4266_1]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [h4197, hlam, p4266_0]
                                    · have p4266_0 := h4266c.1
                                      have p4266_1 := h4266c.2.1
                                      have p4266_2 := h4266c.2.2.1
                                      have p4266_3 := h4266c.2.2.2
                                      linarith only [hlam, p4266_0]
                                  · linarith only [h2, h4, h4008, h4265, hlam, p4199_1, u0elo0]
                                  · linarith only [h2, h4008, h4265, hlam, p4199_1, u0elo0]
                                  · rcases h2bigk with h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c | h4310c
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h2, h4, h4008, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4199_1, p4310_1, u0elo0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h4, hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h1270, hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h1799, hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h0, hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h4131, hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h4133, hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h4135, hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h4140, hc02, hc34, hlam, hphi, ht23, p4310_1]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h4140, hc12, hc34, hlam, hphi, ht23, p4310_1]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h4140, hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h4195, hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      rcases p4310_3 (m.d 0 2) (by simp) with h4326 | h4326
                                      · linarith only [h4326, hlam, p4310_0]
                                      · rcases p4310_3 (m.d 1 2) (by simp) with h4328 | h4328
                                        · linarith only [h4133, h4328, hlam]
                                        · rcases p4310_3 (m.d 2 3) (by simp) with h4330 | h4330
                                          · linarith only [h4140, h4330, hlam]
                                          · linarith only [h4, h4330, hlam]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      rcases p4310_3 (m.d 0 2) (by simp) with h4333 | h4333
                                      · linarith only [h1270, h4333, hlam]
                                      · linarith only [h0, h4333, hlam]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h0, h4, h4140, hc12, hc34, hlam, hphi, ht23, p4310_1]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h0, h1799, h4140, hc12, hc34, hlam, hphi, ht23, p4310_1]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      rcases p4310_3 (m.d 0 2) (by simp) with h4339 | h4339
                                      · linarith only [h4339, hlam, p4310_0]
                                      · rcases p4310_3 (m.d 1 2) (by simp) with h4341 | h4341
                                        · linarith only [h4135, h4341, hlam]
                                        · rcases p4310_3 (m.d 2 3) (by simp) with h4343 | h4343
                                          · linarith only [h4195, h4343, hlam]
                                          · linarith only [h4, h4343, hlam]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      rcases p4310_3 (m.d 0 2) (by simp) with h4346 | h4346
                                      · linarith only [h1799, h4346, hlam]
                                      · linarith only [h0, h4346, hlam]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p4310_1]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [h4197, hlam, p4310_0]
                                    · have p4310_0 := h4310c.1
                                      have p4310_1 := h4310c.2.1
                                      have p4310_2 := h4310c.2.2.1
                                      have p4310_3 := h4310c.2.2.2
                                      linarith only [hlam, p4310_0]
                                  · linarith only [h2, h4265, hlam, p4199_1, u0elo0]
                              · linarith only [h4130, h4262, hlam]
                        · linarith only [h3, h4257, hlam]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [h3, hlam, p4199_0]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        rcases p4199_3 (m.d 0 1) (by simp) with h4356 | h4356
                        · rcases p4199_3 (m.d 0 2) (by simp) with h4357 | h4357
                          · linarith only [h1799, h4357, hlam]
                          · rcases p4199_3 (m.d 0 3) (by simp) with h4359 | h4359
                            · linarith only [h4008, h4359, hlam]
                            · linarith only [h4, h4359, hlam]
                        · linarith only [h0, h4356, hlam]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        rcases p4199_3 (m.d 0 1) (by simp) with h4363 | h4363
                        · rcases p4199_3 (m.d 0 2) (by simp) with h4364 | h4364
                          · linarith only [h1799, h4364, hlam]
                          · rcases p4199_3 (m.d 0 3) (by simp) with h4366 | h4366
                            · linarith only [h4008, h4366, hlam]
                            · rcases p4199_3 (m.d 0 4) (by simp) with h4368 | h4368
                              · rcases p4199_3 (m.d 0 5) (by simp) with h4369 | h4369
                                · rcases h0emin with h4370 | h4370 | h4370 | h4370 | h4370
                                  · rcases h2bigk with h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c | h4371c
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p4371_1]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h4, hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h1270, hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h1799, hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h0, hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h4131, hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h4133, hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h4135, hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h4140, hc02, hc34, hlam, hphi, ht23, p4371_1]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h4140, hc12, hc34, hlam, hphi, ht23, p4371_1]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h4140, hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h4195, hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      rcases p4371_3 (m.d 0 2) (by simp) with h4387 | h4387
                                      · linarith only [h4387, hlam, p4371_0]
                                      · rcases p4371_3 (m.d 1 2) (by simp) with h4389 | h4389
                                        · linarith only [h4133, h4389, hlam]
                                        · rcases p4371_3 (m.d 2 3) (by simp) with h4391 | h4391
                                          · linarith only [h4140, h4391, hlam]
                                          · linarith only [h4, h4391, hlam]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      rcases p4371_3 (m.d 0 2) (by simp) with h4394 | h4394
                                      · linarith only [h1270, h4394, hlam]
                                      · linarith only [h0, h4394, hlam]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h0, h4, h4140, hc12, hc34, hlam, hphi, ht23, p4371_1]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h0, h1799, h4140, hc12, hc34, hlam, hphi, ht23, p4371_1]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      rcases p4371_3 (m.d 0 2) (by simp) with h4400 | h4400
                                      · linarith only [h4400, hlam, p4371_0]
                                      · rcases p4371_3 (m.d 1 2) (by simp) with h4402 | h4402
                                        · linarith only [h4135, h4402, hlam]
                                        · rcases p4371_3 (m.d 2 3) (by simp) with h4404 | h4404
                                          · linarith only [h4195, h4404, hlam]
                                          · linarith only [h4, h4404, hlam]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      rcases p4371_3 (m.d 0 2) (by simp) with h4407 | h4407
                                      · linarith only [h1799, h4407, hlam]
                                      · linarith only [h0, h4407, hlam]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p4371_1]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [h4197, hlam, p4371_0]
                                    · have p4371_0 := h4371c.1
                                      have p4371_1 := h4371c.2.1
                                      have p4371_2 := h4371c.2.2.1
                                      have p4371_3 := h4371c.2.2.2
                                      linarith only [hlam, p4371_0]
                                  · linarith only [h2, h4, h4130, h4370, hlam, p4199_1, u0elo0]
                                  · linarith only [h2, h4130, h4370, hlam, p4199_1, u0elo0]
                                  · rcases h2bigk with h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c | h4415c
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h2, h4, h4130, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4199_1, p4415_1, u0elo0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h4, hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h1270, hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h1799, hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h0, hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h4131, hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h4133, hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h4135, hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h4140, hc02, hc34, hlam, hphi, ht23, p4415_1]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h4140, hc12, hc34, hlam, hphi, ht23, p4415_1]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h4140, hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h4195, hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      rcases p4415_3 (m.d 0 2) (by simp) with h4431 | h4431
                                      · linarith only [h4431, hlam, p4415_0]
                                      · rcases p4415_3 (m.d 1 2) (by simp) with h4433 | h4433
                                        · linarith only [h4133, h4433, hlam]
                                        · rcases p4415_3 (m.d 2 3) (by simp) with h4435 | h4435
                                          · linarith only [h4140, h4435, hlam]
                                          · linarith only [h4, h4435, hlam]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      rcases p4415_3 (m.d 0 2) (by simp) with h4438 | h4438
                                      · linarith only [h1270, h4438, hlam]
                                      · linarith only [h0, h4438, hlam]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h0, h4, h4140, hc12, hc34, hlam, hphi, ht23, p4415_1]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h0, h1799, h4140, hc12, hc34, hlam, hphi, ht23, p4415_1]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      rcases p4415_3 (m.d 0 2) (by simp) with h4444 | h4444
                                      · linarith only [h4444, hlam, p4415_0]
                                      · rcases p4415_3 (m.d 1 2) (by simp) with h4446 | h4446
                                        · linarith only [h4135, h4446, hlam]
                                        · rcases p4415_3 (m.d 2 3) (by simp) with h4448 | h4448
                                          · linarith only [h4195, h4448, hlam]
                                          · linarith only [h4, h4448, hlam]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      rcases p4415_3 (m.d 0 2) (by simp) with h4451 | h4451
                                      · linarith only [h1799, h4451, hlam]
                                      · linarith only [h0, h4451, hlam]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p4415_1]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [h4197, hlam, p4415_0]
                                    · have p4415_0 := h4415c.1
                                      have p4415_1 := h4415c.2.1
                                      have p4415_2 := h4415c.2.2.1
                                      have p4415_3 := h4415c.2.2.2
                                      linarith only [hlam, p4415_0]
                                  · rcases h2bigk with h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c | h4457c
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p4457_1]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h4, hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h1270, hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h1799, hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h0, hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h4131, hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h4133, hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h4135, hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h4140, hc02, hc34, hlam, hphi, ht23, p4457_1]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h4140, hc12, hc34, hlam, hphi, ht23, p4457_1]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h4140, hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h4195, hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      rcases p4457_3 (m.d 0 2) (by simp) with h4473 | h4473
                                      · linarith only [h4473, hlam, p4457_0]
                                      · rcases p4457_3 (m.d 1 2) (by simp) with h4475 | h4475
                                        · linarith only [h4133, h4475, hlam]
                                        · rcases p4457_3 (m.d 2 3) (by simp) with h4477 | h4477
                                          · linarith only [h4140, h4477, hlam]
                                          · linarith only [h4, h4477, hlam]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      rcases p4457_3 (m.d 0 2) (by simp) with h4480 | h4480
                                      · linarith only [h1270, h4480, hlam]
                                      · linarith only [h0, h4480, hlam]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h0, h4, h4140, hc12, hc34, hlam, hphi, ht23, p4457_1]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h0, h1799, h4140, hc12, hc34, hlam, hphi, ht23, p4457_1]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      rcases p4457_3 (m.d 0 2) (by simp) with h4486 | h4486
                                      · linarith only [h4486, hlam, p4457_0]
                                      · rcases p4457_3 (m.d 1 2) (by simp) with h4488 | h4488
                                        · linarith only [h4135, h4488, hlam]
                                        · rcases p4457_3 (m.d 2 3) (by simp) with h4490 | h4490
                                          · linarith only [h4195, h4490, hlam]
                                          · linarith only [h4, h4490, hlam]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      rcases p4457_3 (m.d 0 2) (by simp) with h4493 | h4493
                                      · linarith only [h1799, h4493, hlam]
                                      · linarith only [h0, h4493, hlam]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p4457_1]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [h4197, hlam, p4457_0]
                                    · have p4457_0 := h4457c.1
                                      have p4457_1 := h4457c.2.1
                                      have p4457_2 := h4457c.2.2.1
                                      have p4457_3 := h4457c.2.2.2
                                      linarith only [hlam, p4457_0]
                                · linarith only [h4008, h4369, hlam]
                              · linarith only [h1923, h4368, hlam]
                        · linarith only [h1, h4363, hlam]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [h4130, hlam, p4199_1]
                      · have p4199_0 := h4199c.1
                        have p4199_1 := h4199c.2.1
                        have p4199_2 := h4199c.2.2.1
                        have p4199_3 := h4199c.2.2.2
                        linarith only [hlam, p4199_0]
                    · linarith only [h2, h4139, h4140, h4198, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1270, h4130, h4197, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4506 | h4506
              · linarith only [h1923, h4130, h4131, h4137, h4139, h4506, hc12, hc23, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4508 | h4508
                · linarith only [h1, h4008, h4131, h4506, h4508, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4510 | h4510
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4511 | h4511
                    · rcases h0bigk with h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c | h4512c
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [hlam, p4512_0]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        rcases p4512_3 (m.d 0 1) (by simp) with h4514 | h4514
                        · rcases p4512_3 (m.d 0 2) (by simp) with h4515 | h4515
                          · linarith only [h0, h4515, hlam]
                          · rcases p4512_3 (m.d 0 3) (by simp) with h4517 | h4517
                            · linarith only [h1, h4517, hlam]
                            · linarith only [h4, h4517, hlam]
                        · linarith only [h0, h4514, hlam]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        rcases p4512_3 (m.d 0 1) (by simp) with h4521 | h4521
                        · rcases p4512_3 (m.d 0 2) (by simp) with h4522 | h4522
                          · linarith only [h0, h4522, hlam]
                          · rcases p4512_3 (m.d 0 3) (by simp) with h4524 | h4524
                            · linarith only [h1, h4524, hlam]
                            · rcases p4512_3 (m.d 0 4) (by simp) with h4526 | h4526
                              · linarith only [h2, h4526, hlam]
                              · linarith only [h1923, h4526, hlam]
                        · linarith only [h1, h4521, hlam]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h4130, h4131, h4137, h4139, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4512_1, u0elo0]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h4130, h4131, h4137, h4139, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4512_1, u0elo0]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h0, hlam, p4512_0]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [hlam, p4512_0]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h4, hlam, p4512_0]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h1270, hlam, p4512_1]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h1799, hlam, p4512_0]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h1, hlam, p4512_1]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h0, h4, h4508, h4511, hc12, hc34, hlam, hphi, ht23, p4512_1]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [hlam, p4512_0]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h1923, hlam, p4512_1]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h4008, hlam, p4512_1]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h2, hlam, p4512_0]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        rcases p4512_3 (m.d 0 1) (by simp) with h4543 | h4543
                        · rcases p4512_3 (m.d 0 2) (by simp) with h4544 | h4544
                          · linarith only [h1270, h4544, hlam]
                          · rcases p4512_3 (m.d 0 3) (by simp) with h4546 | h4546
                            · linarith only [h1923, h4546, hlam]
                            · linarith only [h4, h4546, hlam]
                        · linarith only [h0, h4543, hlam]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        rcases p4512_3 (m.d 0 1) (by simp) with h4550 | h4550
                        · rcases p4512_3 (m.d 0 2) (by simp) with h4551 | h4551
                          · linarith only [h1270, h4551, hlam]
                          · rcases p4512_3 (m.d 0 3) (by simp) with h4553 | h4553
                            · linarith only [h1923, h4553, hlam]
                            · rcases p4512_3 (m.d 0 4) (by simp) with h4555 | h4555
                              · rcases p4512_3 (m.d 0 5) (by simp) with h4556 | h4556
                                · linarith only [h4130, h4556, hlam]
                                · linarith only [h4008, h4556, hlam]
                              · linarith only [h1923, h4555, hlam]
                        · linarith only [h1, h4550, hlam]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [hlam, p4512_0]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h4130, h4131, h4137, h4139, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4512_1, u0elo3]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h3, hlam, p4512_0]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        rcases p4512_3 (m.d 0 1) (by simp) with h4564 | h4564
                        · rcases p4512_3 (m.d 0 2) (by simp) with h4565 | h4565
                          · linarith only [h1799, h4565, hlam]
                          · rcases p4512_3 (m.d 0 3) (by simp) with h4567 | h4567
                            · linarith only [h4008, h4567, hlam]
                            · linarith only [h4, h4567, hlam]
                        · linarith only [h0, h4564, hlam]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        rcases p4512_3 (m.d 0 1) (by simp) with h4571 | h4571
                        · rcases p4512_3 (m.d 0 2) (by simp) with h4572 | h4572
                          · linarith only [h1799, h4572, hlam]
                          · rcases p4512_3 (m.d 0 3) (by simp) with h4574 | h4574
                            · linarith only [h4008, h4574, hlam]
                            · rcases p4512_3 (m.d 0 4) (by simp) with h4576 | h4576
                              · rcases p4512_3 (m.d 0 5) (by simp) with h4577 | h4577
                                · rcases h0emin with h4578 | h4578 | h4578 | h4578 | h4578
                                  · rcases h2bigk with h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h4, h4508, h4511, hc12, hc34, hlam, hphi, ht23, p4579_1]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h4, hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h1270, hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h1799, hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h0, hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h4131, hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h4133, hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h4135, hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h4508, h4511, hc02, hc34, hlam, hphi, ht23, p4579_1]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h4508, h4511, hc12, hc34, hlam, hphi, ht23, p4579_1]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h4506, hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h4508, hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      rcases p4579_3 (m.d 0 2) (by simp) with h4595 | h4595
                                      · linarith only [h4595, hlam, p4579_0]
                                      · rcases p4579_3 (m.d 1 2) (by simp) with h4597 | h4597
                                        · linarith only [h4133, h4597, hlam]
                                        · rcases p4579_3 (m.d 2 3) (by simp) with h4599 | h4599
                                          · linarith only [h4506, h4599, hlam]
                                          · linarith only [h4, h4599, hlam]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      rcases p4579_3 (m.d 0 2) (by simp) with h4602 | h4602
                                      · linarith only [h1270, h4602, hlam]
                                      · linarith only [h0, h4602, hlam]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h0, h4, hc12, hc24, hlam, hphi, p4579_1]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h1, h1799, h4131, h4506, hc12, hc34, hlam, hphi, ht23, p4512_1, p4579_1]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      rcases p4579_3 (m.d 0 2) (by simp) with h4608 | h4608
                                      · linarith only [h4608, hlam, p4579_0]
                                      · rcases p4579_3 (m.d 1 2) (by simp) with h4610 | h4610
                                        · linarith only [h4135, h4610, hlam]
                                        · rcases p4579_3 (m.d 2 3) (by simp) with h4612 | h4612
                                          · linarith only [h4508, h4612, hlam]
                                          · linarith only [h4, h4612, hlam]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      rcases p4579_3 (m.d 0 2) (by simp) with h4615 | h4615
                                      · linarith only [h1799, h4615, hlam]
                                      · linarith only [h0, h4615, hlam]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p4579_1]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [h4510, hlam, p4579_0]
                                    · have p4579_0 := h4579c.1
                                      have p4579_1 := h4579c.2.1
                                      have p4579_2 := h4579c.2.2.1
                                      have p4579_3 := h4579c.2.2.2
                                      linarith only [hlam, p4579_0]
                                  · linarith only [h3, h4, h4578, hlam, p4512_1, u0elo0]
                                  · linarith only [h3, h4578, hlam, p4512_1, u0elo0]
                                  · rcases h2bigk with h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c | h4623c
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h2, h4, h4130, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4512_1, p4623_1, u0elo0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h4, hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h1270, hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h1799, hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h0, hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h4131, hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h4133, hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h4135, hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h4506, hc02, hc34, hlam, hphi, ht23, p4623_1]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h4506, hc12, hc34, hlam, hphi, ht23, p4623_1]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h4506, hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h4508, hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      rcases p4623_3 (m.d 0 2) (by simp) with h4639 | h4639
                                      · linarith only [h4639, hlam, p4623_0]
                                      · rcases p4623_3 (m.d 1 2) (by simp) with h4641 | h4641
                                        · linarith only [h4133, h4641, hlam]
                                        · rcases p4623_3 (m.d 2 3) (by simp) with h4643 | h4643
                                          · linarith only [h4506, h4643, hlam]
                                          · linarith only [h4, h4643, hlam]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      rcases p4623_3 (m.d 0 2) (by simp) with h4646 | h4646
                                      · linarith only [h1270, h4646, hlam]
                                      · linarith only [h0, h4646, hlam]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h0, h4, h4506, hc12, hc34, hlam, hphi, ht23, p4623_1]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h0, h1799, h4506, hc12, hc34, hlam, hphi, ht23, p4623_1]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      rcases p4623_3 (m.d 0 2) (by simp) with h4652 | h4652
                                      · linarith only [h4652, hlam, p4623_0]
                                      · rcases p4623_3 (m.d 1 2) (by simp) with h4654 | h4654
                                        · linarith only [h4135, h4654, hlam]
                                        · rcases p4623_3 (m.d 2 3) (by simp) with h4656 | h4656
                                          · linarith only [h4508, h4656, hlam]
                                          · linarith only [h4, h4656, hlam]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      rcases p4623_3 (m.d 0 2) (by simp) with h4659 | h4659
                                      · linarith only [h1799, h4659, hlam]
                                      · linarith only [h0, h4659, hlam]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p4623_1]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [h4510, hlam, p4623_0]
                                    · have p4623_0 := h4623c.1
                                      have p4623_1 := h4623c.2.1
                                      have p4623_2 := h4623c.2.2.1
                                      have p4623_3 := h4623c.2.2.2
                                      linarith only [hlam, p4623_0]
                                  · rcases h2bigk with h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c | h4665c
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p4665_1]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h4, hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h1270, hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h1799, hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h0, hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h4131, hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h4133, hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h4135, hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h4506, hc02, hc34, hlam, hphi, ht23, p4665_1]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h4506, hc12, hc34, hlam, hphi, ht23, p4665_1]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h4506, hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h4508, hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      rcases p4665_3 (m.d 0 2) (by simp) with h4681 | h4681
                                      · linarith only [h4681, hlam, p4665_0]
                                      · rcases p4665_3 (m.d 1 2) (by simp) with h4683 | h4683
                                        · linarith only [h4133, h4683, hlam]
                                        · rcases p4665_3 (m.d 2 3) (by simp) with h4685 | h4685
                                          · linarith only [h4506, h4685, hlam]
                                          · linarith only [h4, h4685, hlam]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      rcases p4665_3 (m.d 0 2) (by simp) with h4688 | h4688
                                      · linarith only [h1270, h4688, hlam]
                                      · linarith only [h0, h4688, hlam]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h0, h4, h4506, hc12, hc34, hlam, hphi, ht23, p4665_1]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h0, h1799, h4506, hc12, hc34, hlam, hphi, ht23, p4665_1]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      rcases p4665_3 (m.d 0 2) (by simp) with h4694 | h4694
                                      · linarith only [h4694, hlam, p4665_0]
                                      · rcases p4665_3 (m.d 1 2) (by simp) with h4696 | h4696
                                        · linarith only [h4135, h4696, hlam]
                                        · rcases p4665_3 (m.d 2 3) (by simp) with h4698 | h4698
                                          · linarith only [h4508, h4698, hlam]
                                          · linarith only [h4, h4698, hlam]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      rcases p4665_3 (m.d 0 2) (by simp) with h4701 | h4701
                                      · linarith only [h1799, h4701, hlam]
                                      · linarith only [h0, h4701, hlam]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p4665_1]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [h4510, hlam, p4665_0]
                                    · have p4665_0 := h4665c.1
                                      have p4665_1 := h4665c.2.1
                                      have p4665_2 := h4665c.2.2.1
                                      have p4665_3 := h4665c.2.2.2
                                      linarith only [hlam, p4665_0]
                                · linarith only [h4008, h4577, hlam]
                              · linarith only [h1923, h4576, hlam]
                        · linarith only [h1, h4571, hlam]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [h4130, hlam, p4512_1]
                      · have p4512_0 := h4512c.1
                        have p4512_1 := h4512c.2.1
                        have p4512_2 := h4512c.2.2.1
                        have p4512_3 := h4512c.2.2.2
                        linarith only [hlam, p4512_0]
                    · linarith only [h1270, h4130, h4506, h4511, hlam]
                  · linarith only [h1270, h4130, h4510, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4714 | h4714
    · linarith only [h0, h4, h4714, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4716 | h4716
      · linarith only [h0, h1270, h4716, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4718 | h4718
        · linarith only [h0, h1799, h4718, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4720 | h4720
          · linarith only [h1, h1923, h4, h4720, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4722 | h4722
            · linarith only [h2, h4130, h4722, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4724 | h4724
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4725 | h4725
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4726 | h4726
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4727 | h4727
                    · linarith only [h0, h1923, h4, h4130, h4724, h4727, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1923, h4, h4726, h4727, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4730 | h4730
                    · linarith only [h0, h1270, h4726, h4730, hc12, hc34, hlam, hphi, ht23]
                    · rcases h0bigk with h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c | h4732c
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [hlam, p4732_0]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        rcases p4732_3 (m.d 0 1) (by simp) with h4734 | h4734
                        · rcases p4732_3 (m.d 0 2) (by simp) with h4735 | h4735
                          · linarith only [h0, h4735, hlam]
                          · rcases p4732_3 (m.d 0 3) (by simp) with h4737 | h4737
                            · linarith only [h1, h4737, hlam]
                            · linarith only [h4, h4737, hlam]
                        · linarith only [h0, h4734, hlam]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        rcases p4732_3 (m.d 0 1) (by simp) with h4741 | h4741
                        · rcases p4732_3 (m.d 0 2) (by simp) with h4742 | h4742
                          · linarith only [h0, h4742, hlam]
                          · rcases p4732_3 (m.d 0 3) (by simp) with h4744 | h4744
                            · linarith only [h1, h4744, hlam]
                            · rcases p4732_3 (m.d 0 4) (by simp) with h4746 | h4746
                              · linarith only [h2, h4746, hlam]
                              · linarith only [h1923, h4746, hlam]
                        · linarith only [h1, h4741, hlam]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        rcases p4732_3 (m.d 0 1) (by simp) with h4750 | h4750
                        · rcases p4732_3 (m.d 0 2) (by simp) with h4751 | h4751
                          · linarith only [h0, h4751, hlam]
                          · rcases p4732_3 (m.d 0 3) (by simp) with h4753 | h4753
                            · linarith only [h1, h4753, hlam]
                            · rcases p4732_3 (m.d 0 4) (by simp) with h4755 | h4755
                              · linarith only [h2, h4755, hlam]
                              · rcases p4732_3 (m.d 0 5) (by simp) with h4757 | h4757
                                · linarith only [h3, h4757, hlam]
                                · linarith only [h4130, h4757, hlam]
                        · linarith only [h2, h4750, hlam]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        rcases p4732_3 (m.d 0 1) (by simp) with h4761 | h4761
                        · rcases p4732_3 (m.d 0 2) (by simp) with h4762 | h4762
                          · linarith only [h0, h4762, hlam]
                          · rcases p4732_3 (m.d 0 3) (by simp) with h4764 | h4764
                            · linarith only [h1, h4764, hlam]
                            · rcases p4732_3 (m.d 0 4) (by simp) with h4766 | h4766
                              · linarith only [h2, h4766, hlam]
                              · rcases p4732_3 (m.d 0 5) (by simp) with h4768 | h4768
                                · linarith only [h3, h4768, hlam]
                                · rcases h0emin with h4770 | h4770 | h4770 | h4770 | h4770
                                  · rcases h2bigk with h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c | h4771c
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [hlam, p4771_0]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h1923, h4, h4724, hc12, hc24, hlam, hphi, p4771_1]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h4, hlam, p4771_0]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h1270, hlam, p4771_0]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h1799, hlam, p4771_0]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h0, hlam, p4771_0]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [hlam, p4771_0]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h4714, hlam, p4771_0]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h4716, hlam, p4771_0]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h4718, hlam, p4771_0]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      rcases p4771_3 (m.d 0 2) (by simp) with h4782 | h4782
                                      · linarith only [h4782, hlam, p4771_0]
                                      · rcases p4771_3 (m.d 1 2) (by simp) with h4784 | h4784
                                        · linarith only [h4714, h4784, hlam]
                                        · rcases p4771_3 (m.d 2 3) (by simp) with h4786 | h4786
                                          · rcases p4771_3 (m.d 2 4) (by simp) with h4787 | h4787
                                            · linarith only [h4724, h4787, hlam]
                                            · linarith only [h1270, h4787, hlam]
                                          · linarith only [h4786, hlam, p4771_0]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      rcases p4771_3 (m.d 0 2) (by simp) with h4791 | h4791
                                      · linarith only [h4, h4791, hlam]
                                      · linarith only [h0, h4791, hlam]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [hlam, p4771_0]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h1270, hc02, hc23, hlam, hphi, p4771_1]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h0, h1799, hc12, hc23, hlam, hphi, p4771_1]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h0, h4726, hc12, hc45, hlam, hphi, ht23, ht34, p4771_1]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h4726, hc12, hc45, hlam, hphi, ht23, ht34, p4771_1]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h4724, hlam, p4771_1]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [hlam, p4771_0]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h4726, hlam, p4771_1]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      rcases p4771_3 (m.d 0 2) (by simp) with h4802 | h4802
                                      · linarith only [h4802, hlam, p4771_0]
                                      · rcases p4771_3 (m.d 1 2) (by simp) with h4804 | h4804
                                        · linarith only [h4718, h4804, hlam]
                                        · rcases p4771_3 (m.d 2 3) (by simp) with h4806 | h4806
                                          · rcases p4771_3 (m.d 2 4) (by simp) with h4807 | h4807
                                            · linarith only [h4726, h4807, hlam]
                                            · linarith only [h1270, h4807, hlam]
                                          · linarith only [h4, h4806, hlam]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      rcases p4771_3 (m.d 0 2) (by simp) with h4811 | h4811
                                      · linarith only [h1799, h4811, hlam]
                                      · linarith only [h0, h4811, hlam]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h4725, hlam, p4771_1]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [h0, h1270, hc12, hc25, hlam, hphi, p4771_1]
                                    · have p4771_0 := h4771c.1
                                      have p4771_1 := h4771c.2.1
                                      have p4771_2 := h4771c.2.2.1
                                      have p4771_3 := h4771c.2.2.2
                                      linarith only [hlam, p4771_0]
                                  · linarith only [h1270, h4130, h4770, hlam, p4732_1, u0elo0]
                                  · linarith only [h1923, h4130, h4770, hlam, p4732_1, u0elo0]
                                  · linarith only [h4130, h4770, hlam, p4732_1, u0elo0]
                                  · linarith only [h4770, hlam, p4732_1, u0elo0]
                        · linarith only [h3, h4761, hlam]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h0, hlam, p4732_0]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [hlam, p4732_0]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h4, hlam, p4732_0]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h1270, hlam, p4732_1]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h1799, hlam, p4732_0]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h1, hlam, p4732_1]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h1923, hc02, hc34, hlam, hphi, ht23, p4732_1]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [hlam, p4732_0]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h1923, hlam, p4732_1]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h4008, hlam, p4732_1]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h2, hlam, p4732_0]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h0, h4130, hc12, hc45, hlam, hphi, ht23, ht34, p4732_1]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h1, h4130, h4714, hc12, hc45, hlam, hphi, ht23, ht34, p4732_1]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [hlam, p4732_0]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h4130, hlam, p4732_0]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h3, hlam, p4732_0]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h0, h4008, h4725, hc12, hc23, hlam, hphi, p4732_1]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h1, h4008, h4714, h4725, hc12, hc23, hlam, hphi, p4732_1]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [h2, h4008, h4714, h4720, h4725, hc12, hc23, hlam, hphi, p4732_1]
                      · have p4732_0 := h4732c.1
                        have p4732_1 := h4732c.2.1
                        have p4732_2 := h4732c.2.2.1
                        have p4732_3 := h4732c.2.2.2
                        linarith only [hlam, p4732_0]
                · linarith only [h1, h1923, h4714, h4724, h4725, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4843 | h4843
                · linarith only [h1, h4008, h4714, h4724, h4843, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4845 | h4845
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4846 | h4846
                    · rcases h0bigk with h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c | h4847c
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [hlam, p4847_0]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        rcases p4847_3 (m.d 0 1) (by simp) with h4849 | h4849
                        · rcases p4847_3 (m.d 0 2) (by simp) with h4850 | h4850
                          · linarith only [h0, h4850, hlam]
                          · rcases p4847_3 (m.d 0 3) (by simp) with h4852 | h4852
                            · linarith only [h1, h4852, hlam]
                            · linarith only [h4, h4852, hlam]
                        · linarith only [h0, h4849, hlam]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        rcases p4847_3 (m.d 0 1) (by simp) with h4856 | h4856
                        · rcases p4847_3 (m.d 0 2) (by simp) with h4857 | h4857
                          · linarith only [h0, h4857, hlam]
                          · rcases p4847_3 (m.d 0 3) (by simp) with h4859 | h4859
                            · linarith only [h1, h4859, hlam]
                            · rcases p4847_3 (m.d 0 4) (by simp) with h4861 | h4861
                              · linarith only [h2, h4861, hlam]
                              · linarith only [h1923, h4861, hlam]
                        · linarith only [h1, h4856, hlam]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        rcases p4847_3 (m.d 0 1) (by simp) with h4865 | h4865
                        · rcases p4847_3 (m.d 0 2) (by simp) with h4866 | h4866
                          · linarith only [h0, h4866, hlam]
                          · rcases p4847_3 (m.d 0 3) (by simp) with h4868 | h4868
                            · linarith only [h1, h4868, hlam]
                            · rcases p4847_3 (m.d 0 4) (by simp) with h4870 | h4870
                              · linarith only [h2, h4870, hlam]
                              · rcases p4847_3 (m.d 0 5) (by simp) with h4872 | h4872
                                · linarith only [h3, h4872, hlam]
                                · linarith only [h4130, h4872, hlam]
                        · linarith only [h2, h4865, hlam]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        rcases p4847_3 (m.d 0 1) (by simp) with h4876 | h4876
                        · rcases p4847_3 (m.d 0 2) (by simp) with h4877 | h4877
                          · linarith only [h0, h4877, hlam]
                          · rcases p4847_3 (m.d 0 3) (by simp) with h4879 | h4879
                            · linarith only [h1, h4879, hlam]
                            · rcases p4847_3 (m.d 0 4) (by simp) with h4881 | h4881
                              · linarith only [h2, h4881, hlam]
                              · rcases p4847_3 (m.d 0 5) (by simp) with h4883 | h4883
                                · linarith only [h3, h4883, hlam]
                                · rcases h0emin with h4885 | h4885 | h4885 | h4885 | h4885
                                  · rcases h2bigk with h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c | h4886c
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h4, h4843, h4846, hc12, hc34, hlam, hphi, ht23, p4886_1]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h4, hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h1270, hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h1799, hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h0, hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h4714, hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h4716, hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h4718, hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h4843, h4846, hc02, hc34, hlam, hphi, ht23, p4886_1]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h4843, h4846, hc12, hc34, hlam, hphi, ht23, p4886_1]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h4724, hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h4843, hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      rcases p4886_3 (m.d 0 2) (by simp) with h4902 | h4902
                                      · linarith only [h4902, hlam, p4886_0]
                                      · rcases p4886_3 (m.d 1 2) (by simp) with h4904 | h4904
                                        · linarith only [h4716, h4904, hlam]
                                        · rcases p4886_3 (m.d 2 3) (by simp) with h4906 | h4906
                                          · linarith only [h4724, h4906, hlam]
                                          · linarith only [h4, h4906, hlam]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      rcases p4886_3 (m.d 0 2) (by simp) with h4909 | h4909
                                      · linarith only [h1270, h4909, hlam]
                                      · linarith only [h0, h4909, hlam]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h0, h4, h4724, hc12, hc34, hlam, hphi, ht23, p4886_1]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h0, h1799, h4724, hc12, hc34, hlam, hphi, ht23, p4886_1]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      rcases p4886_3 (m.d 0 2) (by simp) with h4915 | h4915
                                      · linarith only [h4915, hlam, p4886_0]
                                      · rcases p4886_3 (m.d 1 2) (by simp) with h4917 | h4917
                                        · linarith only [h4718, h4917, hlam]
                                        · rcases p4886_3 (m.d 2 3) (by simp) with h4919 | h4919
                                          · linarith only [h4843, h4919, hlam]
                                          · linarith only [h4, h4919, hlam]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      rcases p4886_3 (m.d 0 2) (by simp) with h4922 | h4922
                                      · linarith only [h1799, h4922, hlam]
                                      · linarith only [h0, h4922, hlam]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p4886_1]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [h4845, hlam, p4886_0]
                                    · have p4886_0 := h4886c.1
                                      have p4886_1 := h4886c.2.1
                                      have p4886_2 := h4886c.2.2.1
                                      have p4886_3 := h4886c.2.2.2
                                      linarith only [hlam, p4886_0]
                                  · linarith only [h1799, h4885, hlam, p4847_1, u0elo0]
                                  · linarith only [h4008, h4885, hlam, p4847_1, u0elo0]
                                  · linarith only [h4130, h4885, hlam, p4847_1, u0elo0]
                                  · linarith only [h4885, hlam, p4847_1, u0elo0]
                        · linarith only [h3, h4876, hlam]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h0, hlam, p4847_0]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [hlam, p4847_0]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h4, hlam, p4847_0]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h1270, hlam, p4847_1]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h1799, hlam, p4847_0]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h1, hlam, p4847_1]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h0, h1923, hc12, hc34, hlam, hphi, ht23, p4847_1]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [hlam, p4847_0]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h1923, hlam, p4847_1]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h4008, hlam, p4847_1]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h2, hlam, p4847_0]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h0, h4130, hc12, hc45, hlam, hphi, ht23, ht34, p4847_1]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h4130, hc03, hc45, hlam, hphi, ht34, p4847_1]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [hlam, p4847_0]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h4130, hlam, p4847_0]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h3, hlam, p4847_0]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h0, h4130, h4724, h4845, hc12, hc34, hlam, hphi, ht23, p4847_1]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h1, h4130, h4714, h4724, h4845, hc12, hc34, hlam, hphi, ht23, p4847_1]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [h2, h4130, h4714, h4720, h4724, h4845, hc12, hc34, hlam, hphi, ht23, p4847_1]
                      · have p4847_0 := h4847c.1
                        have p4847_1 := h4847c.2.1
                        have p4847_2 := h4847c.2.2.1
                        have p4847_3 := h4847c.2.2.2
                        linarith only [hlam, p4847_0]
                    · linarith only [h4724, h4845, h4846, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4954 | h4954
                    · linarith only [h0, h4, h4724, h4845, h4954, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h4, h4724, h4954, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
