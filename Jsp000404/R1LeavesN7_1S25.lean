import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S23
import Jsp000404.R1LeavesN7_1S24

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 31062000 in
set_option maxHeartbeats 31062000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h14500 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h15153 | h15153
  · rcases m.htr 0 2 3 (by decide) (by decide) with h15154 | h15154
    · linarith only [h0, h1, h15154, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h15156 | h15156
      · linarith only [h0, h14500, h15156, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h15158 | h15158
        · rcases m.htr 0 3 4 (by decide) (by decide) with h15159 | h15159
          · rcases m.htr 0 3 5 (by decide) (by decide) with h15160 | h15160
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15161 | h15161
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15162 | h15162
                · linarith only [h0, h1, h15154, h15162, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15164 | h15164
                  · linarith only [h0, h14500, h15156, h15164, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15166 | h15166
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15167 | h15167
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h15168 | h15168
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h15169 | h15169
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h15170 | h15170
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h15171 | h15171
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h15172 | h15172
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h15173 | h15173
                                  · rcases h0bigk with h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c | h15174c
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [hlam, p15174_0]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h14500, h15162, h15167, hc02, hc23, hlam, hphi, p15174_1]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h1, hlam, p15174_0]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h14500, hlam, p15174_1]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      rcases p15174_3 (m.d 0 1) (by simp) with h15179 | h15179
                                      · rcases p15174_3 (m.d 0 2) (by simp) with h15180 | h15180
                                        · linarith only [h0, h15180, hlam]
                                        · linarith only [h15158, h15180, hlam]
                                      · linarith only [h15153, h15179, hlam]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h0, hlam, p15174_0]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [hlam, p15174_0]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h15154, hlam, p15174_0]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h15156, hlam, p15174_1]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      rcases p15174_3 (m.d 0 1) (by simp) with h15188 | h15188
                                      · rcases p15174_3 (m.d 0 2) (by simp) with h15189 | h15189
                                        · rcases p15174_3 (m.d 0 3) (by simp) with h15190 | h15190
                                          · rcases p15174_3 (m.d 0 4) (by simp) with h15191 | h15191
                                            · rcases p15174_3 (m.d 0 5) (by simp) with h15192 | h15192
                                              · linarith only [h15158, h15192, hlam]
                                              · rcases h2bigk with h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c | h15194c
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h0, h14500, h15162, h15167, hc12, hc23, hlam, hphi, p15194_1]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h15154, hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h15156, hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  rcases p15194_3 (m.d 0 2) (by simp) with h15199 | h15199
                                                  · rcases p15194_3 (m.d 1 2) (by simp) with h15200 | h15200
                                                    · linarith only [h0, h15200, hlam]
                                                    · linarith only [h15166, h15200, hlam]
                                                  · linarith only [h15199, hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h0, hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h15162, hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h15164, hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h0, h14500, h15162, h15167, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p15194_1]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h15153, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p15174_1, p15194_1]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  rcases p15194_3 (m.d 0 2) (by simp) with h15210 | h15210
                                                  · linarith only [h15154, h15210, hlam]
                                                  · linarith only [h0, h15210, hlam]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h14500, h15164, hc01, hc23, hlam, hphi, ht12, p15194_1]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h0, h14500, h15153, h15162, h15166, h15167, hlam, p15174_1, p15194_2]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h15153, h15166, h15171, h15173, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p15174_1, p15194_1]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  rcases p15194_3 (m.d 0 2) (by simp) with h15217 | h15217
                                                  · linarith only [h15156, h15217, hlam]
                                                  · linarith only [h0, h15217, hlam]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h15170, hlam, p15194_1]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h15153, h15156, h15166, hlam, p15174_1, p15194_2]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h15158, hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h15166, hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h15171, hlam, p15194_1]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [h15172, hlam, p15194_0]
                                                · have p15194_0 := h15194c.1
                                                  have p15194_1 := h15194c.2.1
                                                  have p15194_2 := h15194c.2.2.1
                                                  have p15194_3 := h15194c.2.2.2
                                                  linarith only [hlam, p15194_0]
                                            · linarith only [h15161, h15191, hlam]
                                          · linarith only [h15160, h15190, hlam]
                                        · linarith only [h15158, h15189, hlam]
                                      · linarith only [h15153, h15188, hlam]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h0, h15166, h15171, h15173, hc03, hc45, hlam, hphi, ht0b, ht5b, p15174_1]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      rcases p15174_3 (m.d 0 1) (by simp) with h15233 | h15233
                                      · linarith only [h1, h15233, hlam]
                                      · linarith only [h0, h15233, hlam]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [hlam, p15174_0]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h0, h14500, h15166, h15171, h15173, hc03, hc45, hlam, hphi, ht0b, ht5b, p15174_1]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      rcases p15174_3 (m.d 0 1) (by simp) with h15238 | h15238
                                      · linarith only [h1, h15238, hlam]
                                      · linarith only [h15153, h15238, hlam]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h0, h15166, h15171, h15173, hc04, hc45, hlam, hphi, ht0b, ht5b, p15174_1]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      rcases p15174_3 (m.d 0 1) (by simp) with h15242 | h15242
                                      · linarith only [h14500, h15242, hlam]
                                      · linarith only [h0, h15242, hlam]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h15159, hlam, p15174_0]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [hlam, p15174_0]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      rcases p15174_3 (m.d 0 1) (by simp) with h15247 | h15247
                                      · linarith only [h14500, h15247, hlam]
                                      · linarith only [h15153, h15247, hlam]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h15153, hlam, p15174_0]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h15158, hlam, p15174_1]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h15160, hlam, p15174_0]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [h15161, hlam, p15174_1]
                                    · have p15174_0 := h15174c.1
                                      have p15174_1 := h15174c.2.1
                                      have p15174_2 := h15174c.2.2.1
                                      have p15174_3 := h15174c.2.2.2
                                      linarith only [hlam, p15174_0]
                                  · linarith only [h0, h14500, h15162, h15166, h15167, h15172, h15173, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h14500, h15153, h15156, h15167, h15169, h15172, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · linarith only [h0, h14500, h15162, h15167, h15171, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h14500, h15162, h15166, h15167, h15170, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h14500, h15166, h15169, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h0, h14500, h15166, h15167, h15168, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1, h15159, h15167, hlam]
                    · linarith only [h0, h14500, h15158, h15164, h15166, hc12, hc24, hlam, hphi]
              · linarith only [h14500, h15153, h15161, hlam]
            · linarith only [h0, h1, h15158, h15160, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h15265 | h15265
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15266 | h15266
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15267 | h15267
                · linarith only [h0, h1, h15159, h15267, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15269 | h15269
                  · linarith only [h0, h1, h15156, h15159, h15269, hc02, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15271 | h15271
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15272 | h15272
                      · linarith only [h0, h1, h15159, h15267, h15271, h15272, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1, h15271, h15272, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h14500, h15158, h15269, h15271, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1, h15158, h15159, h15266, hlam]
            · linarith only [h0, h1, h15158, h15265, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h15278 | h15278
          · rcases m.htr 0 3 5 (by decide) (by decide) with h15279 | h15279
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15280 | h15280
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15281 | h15281
                · linarith only [h0, h1, h15154, h15281, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15283 | h15283
                  · linarith only [h0, h15156, h15283, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15285 | h15285
                    · linarith only [h0, h15158, h15285, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15287 | h15287
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h15288 | h15288
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h15289 | h15289
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h15290 | h15290
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h15291 | h15291
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h15292 | h15292
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h15293 | h15293
                                  · rcases h0bigk with h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c | h15294c
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [hlam, p15294_0]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h14500, h15281, h15287, hc02, hc23, hlam, hphi, p15294_1]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h1, hlam, p15294_0]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h14500, hlam, p15294_1]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h0, h14500, h15158, h15281, h15287, hc12, hc23, hlam, hphi, p15294_1]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h0, hlam, p15294_0]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [hlam, p15294_0]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h15154, hlam, p15294_0]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h15156, hlam, p15294_1]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h15158, hlam, p15294_0]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h0, h1, h15281, hc12, hc23, hlam, hphi, p15294_1]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      rcases p15294_3 (m.d 0 1) (by simp) with h15306 | h15306
                                      · linarith only [h1, h15306, hlam]
                                      · linarith only [h0, h15306, hlam]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [hlam, p15294_0]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h1, h14500, h15153, h15281, h15285, hc12, hc23, hlam, hphi, p15294_1]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      rcases p15294_3 (m.d 0 1) (by simp) with h15311 | h15311
                                      · linarith only [h1, h15311, hlam]
                                      · linarith only [h15153, h15311, hlam]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h14500, h15153, h15283, h15285, hc12, hc24, hlam, hphi, p15294_1]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      rcases p15294_3 (m.d 0 1) (by simp) with h15315 | h15315
                                      · linarith only [h14500, h15315, hlam]
                                      · linarith only [h0, h15315, hlam]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h15278, hlam, p15294_0]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [hlam, p15294_0]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      rcases p15294_3 (m.d 0 1) (by simp) with h15320 | h15320
                                      · linarith only [h14500, h15320, hlam]
                                      · linarith only [h15153, h15320, hlam]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h15153, hlam, p15294_0]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h0, h1, h15153, h15281, hc12, hc23, hlam, hphi, p15294_1]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h15279, hlam, p15294_0]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [h15280, hlam, p15294_1]
                                    · have p15294_0 := h15294c.1
                                      have p15294_1 := h15294c.2.1
                                      have p15294_2 := h15294c.2.2.1
                                      have p15294_3 := h15294c.2.2.2
                                      linarith only [hlam, p15294_0]
                                  · rcases h0bigk with h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c | h15328c
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [hlam, p15328_0]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h0, h14500, h15281, h15287, hc12, hc23, hlam, hphi, p15328_1]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h1, hlam, p15328_0]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h14500, hlam, p15328_1]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h14500, h15153, h15281, h15287, h15289, h15293, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15328_1]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h0, hlam, p15328_0]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [hlam, p15328_0]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h15154, hlam, p15328_0]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h15156, hlam, p15328_1]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h15158, hlam, p15328_0]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h0, h1, h15281, hc12, hc23, hlam, hphi, p15328_1]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      rcases p15328_3 (m.d 0 1) (by simp) with h15340 | h15340
                                      · linarith only [h1, h15340, hlam]
                                      · linarith only [h0, h15340, hlam]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [hlam, p15328_0]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h1, h14500, h15153, h15281, h15289, h15293, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15328_1]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      rcases p15328_3 (m.d 0 1) (by simp) with h15345 | h15345
                                      · linarith only [h1, h15345, hlam]
                                      · linarith only [h15153, h15345, hlam]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h15153, h15289, h15293, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p15328_1]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      rcases p15328_3 (m.d 0 1) (by simp) with h15349 | h15349
                                      · linarith only [h14500, h15349, hlam]
                                      · linarith only [h0, h15349, hlam]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h15278, hlam, p15328_0]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [hlam, p15328_0]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      rcases p15328_3 (m.d 0 1) (by simp) with h15354 | h15354
                                      · linarith only [h14500, h15354, hlam]
                                      · linarith only [h15153, h15354, hlam]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h15153, hlam, p15328_0]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h0, h1, h15153, h15281, hc12, hc23, hlam, hphi, p15328_1]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h15279, hlam, p15328_0]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [h15280, hlam, p15328_1]
                                    · have p15328_0 := h15328c.1
                                      have p15328_1 := h15328c.2.1
                                      have p15328_2 := h15328c.2.2.1
                                      have p15328_3 := h15328c.2.2.2
                                      linarith only [hlam, p15328_0]
                                · linarith only [h0, h14500, h15153, h15156, h15281, h15287, h15289, h15292, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h14500, h15281, h15287, h15291, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h14500, h15281, h15287, h15290, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h14500, h15153, h15285, h15289, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h14500, h15153, h15285, h15287, h15288, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h15278, h15287, hlam]
              · linarith only [h14500, h15153, h15280, hlam]
            · linarith only [h1, h15153, h15279, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h15370 | h15370
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15371 | h15371
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15372 | h15372
                · linarith only [h0, h1, h15154, h15372, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15374 | h15374
                  · linarith only [h0, h15156, h15374, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15376 | h15376
                    · linarith only [h0, h15158, h15376, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15378 | h15378
                      · linarith only [h1, h15153, h15278, h15372, h15376, h15378, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h15153, h15376, h15378, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h15153, h15278, h15371, hlam]
            · linarith only [h1, h15153, h15370, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h15383 | h15383
    · linarith only [h0, h1, h15383, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h15385 | h15385
      · linarith only [h0, h14500, h15385, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h15387 | h15387
        · linarith only [h0, h15153, h15387, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h15389 | h15389
          · rcases m.htr 0 3 5 (by decide) (by decide) with h15390 | h15390
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15391 | h15391
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15392 | h15392
                · linarith only [h0, h1, h15383, h15392, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15394 | h15394
                  · linarith only [h0, h1, h15385, h15391, h15392, h15394, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15396 | h15396
                    · linarith only [h0, h15153, h15387, h15396, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15398 | h15398
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h15399 | h15399
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h15400 | h15400
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h15401 | h15401
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h15402 | h15402
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h15403 | h15403
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h15404 | h15404
                                  · rcases h0bigk with h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c | h15405c
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [hlam, p15405_0]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h15153, h15392, h15398, h15400, hc02, hc23, hlam, hphi, p15405_1]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h1, hlam, p15405_0]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h14500, hlam, p15405_1]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h15153, hlam, p15405_1]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h0, hlam, p15405_0]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [hlam, p15405_0]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h15383, hlam, p15405_0]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h15385, hlam, p15405_1]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h15387, hlam, p15405_0]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h0, h1, h15392, hc12, hc23, hlam, hphi, p15405_1]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      rcases p15405_3 (m.d 0 1) (by simp) with h15417 | h15417
                                      · linarith only [h1, h15417, hlam]
                                      · linarith only [h0, h15417, hlam]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [hlam, p15405_0]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h0, h1, h14500, h15392, hc12, hc23, hlam, hphi, p15405_1]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h0, h1, h15153, h15392, hc12, hc23, hlam, hphi, p15405_1]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h0, h14500, h15394, hc12, hc24, hlam, hphi, p15405_1]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      rcases p15405_3 (m.d 0 1) (by simp) with h15424 | h15424
                                      · linarith only [h14500, h15424, hlam]
                                      · linarith only [h0, h15424, hlam]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h15389, hlam, p15405_0]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [hlam, p15405_0]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h0, h1, h15153, h15389, h15392, hc12, hc23, hlam, hphi, p15405_1]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h0, h15153, h15396, hc12, hc25, hlam, hphi, p15405_1]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      rcases p15405_3 (m.d 0 1) (by simp) with h15431 | h15431
                                      · linarith only [h15153, h15431, hlam]
                                      · linarith only [h0, h15431, hlam]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h15390, hlam, p15405_0]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [h15391, hlam, p15405_1]
                                    · have p15405_0 := h15405c.1
                                      have p15405_1 := h15405c.2.1
                                      have p15405_2 := h15405c.2.2.1
                                      have p15405_3 := h15405c.2.2.2
                                      linarith only [hlam, p15405_0]
                                  · rcases h0bigk with h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c | h15437c
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [hlam, p15437_0]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h0, h1, h15392, hc12, hc23, hlam, hphi, p15437_1]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h1, hlam, p15437_0]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h14500, hlam, p15437_1]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h15153, hlam, p15437_1]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h0, hlam, p15437_0]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [hlam, p15437_0]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h15383, hlam, p15437_0]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h15385, hlam, p15437_1]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h15387, hlam, p15437_0]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h0, h1, h15392, hc12, hc23, hlam, hphi, p15437_1]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      rcases p15437_3 (m.d 0 1) (by simp) with h15449 | h15449
                                      · linarith only [h1, h15449, hlam]
                                      · linarith only [h0, h15449, hlam]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [hlam, p15437_0]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h0, h1, h14500, h15392, hc12, hc23, hlam, hphi, p15437_1]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h0, h1, h15153, h15392, hc12, hc23, hlam, hphi, p15437_1]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h0, h14500, h15392, h15398, hc12, hc23, hlam, hphi, p15437_1]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      rcases p15437_3 (m.d 0 1) (by simp) with h15456 | h15456
                                      · linarith only [h14500, h15456, hlam]
                                      · linarith only [h0, h15456, hlam]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h15389, hlam, p15437_0]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [hlam, p15437_0]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h0, h14500, h15153, h15392, h15398, hc12, hc23, hlam, hphi, p15437_1]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h0, h15153, h15392, h15398, h15400, hc12, hc23, hlam, hphi, p15437_1]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      rcases p15437_3 (m.d 0 1) (by simp) with h15463 | h15463
                                      · linarith only [h15153, h15463, hlam]
                                      · linarith only [h0, h15463, hlam]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h15390, hlam, p15437_0]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [h15391, hlam, p15437_1]
                                    · have p15437_0 := h15437c.1
                                      have p15437_1 := h15437c.2.1
                                      have p15437_2 := h15437c.2.2.1
                                      have p15437_3 := h15437c.2.2.2
                                      linarith only [hlam, p15437_0]
                                · linarith only [h0, h14500, h15385, h15391, h15392, h15398, h15403, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h1, h15392, h15402, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h15392, h15401, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h14500, h15391, h15400, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h1, h15390, h15399, hlam]
                      · linarith only [h1, h15389, h15398, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15475 | h15475
                · linarith only [h0, h14500, h15391, h15475, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15477 | h15477
                  · linarith only [h0, h15385, h15477, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15479 | h15479
                    · linarith only [h0, h15387, h15479, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15481 | h15481
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h15482 | h15482
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h15483 | h15483
                          · linarith only [h0, h14500, h15391, h15475, h15481, h15483, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h14500, h15483, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h1, h15390, h15482, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h15481, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15488 | h15488
              · linarith only [h15389, h15390, h15488, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15490 | h15490
                · linarith only [h0, h14500, h15488, h15490, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15492 | h15492
                  · linarith only [h0, h14500, h15385, h15488, h15492, hc02, hc45, hlam, hphi, ht23, ht34]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15494 | h15494
                    · linarith only [h0, h15153, h15387, h15494, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15496 | h15496
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h15497 | h15497
                        · linarith only [h0, h14500, h15389, h15390, h15490, h15497, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h15497, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h15389, h15496, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h15501 | h15501
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15502 | h15502
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15503 | h15503
                · linarith only [h0, h15383, h15503, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15505 | h15505
                  · linarith only [h0, h15385, h15505, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15507 | h15507
                    · linarith only [h0, h15387, h15507, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15509 | h15509
                      · linarith only [h0, h15153, h15389, h15501, h15503, h15509, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h15509, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h15389, h15501, h15502, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h15513 | h15513
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15514 | h15514
                · linarith only [h0, h1, h15501, h15514, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15516 | h15516
                  · linarith only [h0, h15385, h15516, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15518 | h15518
                    · linarith only [h0, h15387, h15518, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15520 | h15520
                      · linarith only [h0, h1, h15389, h15514, h15520, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h15520, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15523 | h15523
                · linarith only [h0, h1, h15389, h15513, h15523, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h15525 | h15525
                  · linarith only [h0, h1, h15385, h15389, h15513, h15525, hc02, hc45, hlam, hphi, ht23, ht34]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15527 | h15527
                    · linarith only [h0, h1, h15387, h15389, h15513, h15527, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h15529 | h15529
                      · linarith only [h0, h1, h15389, h15523, h15529, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h15529, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 31062000 in
set_option maxHeartbeats 31062000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h14500 | h14500
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s0_x1_x0 m hb0 hb2 hb3 hb5 hg0 h1 h14500
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s0_x1_x1 m hb0 hb2 hb3 hb5 hg0 h1 h14500

set_option maxHeartbeats 31062000 in
set_option maxHeartbeats 31062000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s0_x0 m hb0 hb2 hb3 hb5 hg0 h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s0_x1 m hb0 hb2 hb3 hb5 hg0 h1

end R2N4
