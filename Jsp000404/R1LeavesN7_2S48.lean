import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S47

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16917 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h16918 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h16919 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h16920 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h16921 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h16922 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h14396 := hg14396
  rcases m.htr 1 2 3 (by decide) (by decide) with h17118 | h17118
  · rcases m.htr 1 2 4 (by decide) (by decide) with h17119 | h17119
    · rcases m.htr 1 2 5 (by decide) (by decide) with h17120 | h17120
      · rcases m.htr 1 3 4 (by decide) (by decide) with h17121 | h17121
        · rcases m.htr 1 3 5 (by decide) (by decide) with h17122 | h17122
          · rcases m.htr 1 4 5 (by decide) (by decide) with h17123 | h17123
            · linarith only [h14396, h16915, h16922, h17123, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h17125 | h17125
              · rcases m.htr 2 3 5 (by decide) (by decide) with h17126 | h17126
                · rcases m.htr 2 4 5 (by decide) (by decide) with h17127 | h17127
                  · linarith only [h16915, h16922, h17119, h17127, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17129 | h17129
                    · linarith only [h16915, h16922, h17119, h17125, h17129, hlam]
                    · rcases h0bigk with h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c | h17131c
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [hlam, p17131_0]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [h0, hlam, p17131_1]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [h14396, hlam, p17131_0]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        rcases p17131_3 (m.d 0 1) (by simp) with h17135 | h17135
                        · rcases p17131_3 (m.d 0 2) (by simp) with h17136 | h17136
                          · rcases p17131_3 (m.d 0 3) (by simp) with h17137 | h17137
                            · rcases p17131_3 (m.d 0 4) (by simp) with h17138 | h17138
                              · linarith only [h16915, h17138, hlam]
                              · rcases p17131_3 (m.d 0 5) (by simp) with h17140 | h17140
                                · linarith only [h16916, h17140, hlam]
                                · linarith only [h16922, h17140, hlam]
                            · linarith only [h16920, h17137, hlam]
                          · linarith only [h16918, h17136, hlam]
                        · linarith only [h16915, h17135, hlam]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        rcases p17131_3 (m.d 0 1) (by simp) with h17146 | h17146
                        · rcases p17131_3 (m.d 0 2) (by simp) with h17147 | h17147
                          · rcases p17131_3 (m.d 0 3) (by simp) with h17148 | h17148
                            · rcases p17131_3 (m.d 0 4) (by simp) with h17149 | h17149
                              · linarith only [h16915, h17149, hlam]
                              · rcases p17131_3 (m.d 0 5) (by simp) with h17151 | h17151
                                · linarith only [h16916, h17151, hlam]
                                · rcases h2bigk with h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c | h17153c
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h0, hlam, p17153_1]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    rcases p17153_3 (m.d 0 2) (by simp) with h17156 | h17156
                                    · rcases p17153_3 (m.d 1 2) (by simp) with h17157 | h17157
                                      · rcases p17153_3 (m.d 2 3) (by simp) with h17158 | h17158
                                        · linarith only [h17158, hlam, p17153_0]
                                        · rcases p17153_3 (m.d 2 4) (by simp) with h17160 | h17160
                                          · linarith only [h16918, h17160, hlam]
                                          · rcases p17153_3 (m.d 2 5) (by simp) with h17162 | h17162
                                            · linarith only [h16919, h17162, hlam]
                                            · rcases h3bigk with h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c | h17164c
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h14396, hlam, p17164_1]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h16917, hlam, p17153_2, p17164_1]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                rcases p17164_3 (m.d 0 3) (by simp) with h17168 | h17168
                                                · rcases p17164_3 (m.d 1 3) (by simp) with h17169 | h17169
                                                  · rcases p17164_3 (m.d 2 3) (by simp) with h17170 | h17170
                                                    · linarith only [h16917, h17170, hlam]
                                                    · linarith only [h17125, h17170, hlam]
                                                  · linarith only [h17121, h17169, hlam]
                                                · linarith only [h17168, hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                rcases p17164_3 (m.d 0 3) (by simp) with h17175 | h17175
                                                · rcases p17164_3 (m.d 1 3) (by simp) with h17176 | h17176
                                                  · rcases p17164_3 (m.d 2 3) (by simp) with h17177 | h17177
                                                    · linarith only [h16917, h17177, hlam]
                                                    · linarith only [h17126, h17177, hlam]
                                                  · linarith only [h17122, h17176, hlam]
                                                · linarith only [h17175, hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h14396, h17118, hc01, hc12, hlam, hphi, p17164_1]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h17118, h17126, h17129, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17164_1]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                rcases p17164_3 (m.d 0 3) (by simp) with h17185 | h17185
                                                · linarith only [h14396, h17185, hlam]
                                                · linarith only [h16920, h17185, hlam]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                rcases p17164_3 (m.d 0 3) (by simp) with h17188 | h17188
                                                · linarith only [h14396, h17188, hlam]
                                                · linarith only [h16921, h17188, hlam]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h16917, hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h17118, hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17153_1, p17164_1]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h0, h17129, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17153_1, p17164_1]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h16920, hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h17121, hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h17125, hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h17129, hlam, p17164_1]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h16921, hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h17122, hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h17126, hlam, p17164_0]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [h16921, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p17164_1]
                                              · have p17164_0 := h17164c.1
                                                have p17164_1 := h17164c.2.1
                                                have p17164_2 := h17164c.2.2.1
                                                have p17164_3 := h17164c.2.2.2
                                                linarith only [hlam, p17164_0]
                                      · linarith only [h17118, h17157, hlam]
                                    · linarith only [h17156, hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    rcases p17153_3 (m.d 0 2) (by simp) with h17208 | h17208
                                    · rcases p17153_3 (m.d 1 2) (by simp) with h17209 | h17209
                                      · rcases p17153_3 (m.d 2 3) (by simp) with h17210 | h17210
                                        · linarith only [h16917, h17210, hlam]
                                        · linarith only [h17125, h17210, hlam]
                                      · linarith only [h17119, h17209, hlam]
                                    · linarith only [h17208, hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    rcases p17153_3 (m.d 0 2) (by simp) with h17215 | h17215
                                    · rcases p17153_3 (m.d 1 2) (by simp) with h17216 | h17216
                                      · rcases p17153_3 (m.d 2 3) (by simp) with h17217 | h17217
                                        · linarith only [h16917, h17217, hlam]
                                        · linarith only [h17126, h17217, hlam]
                                      · linarith only [h17120, h17216, hlam]
                                    · linarith only [h17215, hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h0, h16915, h16922, h17119, h17125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17131_1, p17153_1]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    rcases p17153_3 (m.d 0 2) (by simp) with h17224 | h17224
                                    · linarith only [h0, h17224, hlam]
                                    · linarith only [h16917, h17224, hlam]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h0, h16915, h16922, h17119, hlam, p17131_1, p17153_2]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h14396, h16916, h17118, h17120, hlam, p17131_1, p17153_2]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h16917, hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h17118, hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    rcases p17153_3 (m.d 0 2) (by simp) with h17232 | h17232
                                    · rcases p17153_3 (m.d 1 2) (by simp) with h17233 | h17233
                                      · rcases p17153_3 (m.d 2 3) (by simp) with h17234 | h17234
                                        · rcases p17153_3 (m.d 2 4) (by simp) with h17235 | h17235
                                          · linarith only [h17125, h17235, hlam]
                                          · rcases p17153_3 (m.d 2 5) (by simp) with h17237 | h17237
                                            · linarith only [h17126, h17237, hlam]
                                            · linarith only [h17127, h17237, hlam]
                                        · linarith only [h17125, h17234, hlam]
                                      · linarith only [h17119, h17233, hlam]
                                    · linarith only [h16918, h17232, hlam]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    rcases p17153_3 (m.d 0 2) (by simp) with h17243 | h17243
                                    · rcases p17153_3 (m.d 1 2) (by simp) with h17244 | h17244
                                      · rcases p17153_3 (m.d 2 3) (by simp) with h17245 | h17245
                                        · rcases p17153_3 (m.d 2 4) (by simp) with h17246 | h17246
                                          · linarith only [h17125, h17246, hlam]
                                          · rcases p17153_3 (m.d 2 5) (by simp) with h17248 | h17248
                                            · linarith only [h17126, h17248, hlam]
                                            · rcases h3bigk with h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c | h17250c
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h14396, hlam, p17250_1]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h17126, h17129, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p17153_1, p17250_1]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                rcases p17250_3 (m.d 0 3) (by simp) with h17254 | h17254
                                                · rcases p17250_3 (m.d 1 3) (by simp) with h17255 | h17255
                                                  · rcases p17250_3 (m.d 2 3) (by simp) with h17256 | h17256
                                                    · linarith only [h16917, h17256, hlam]
                                                    · linarith only [h17125, h17256, hlam]
                                                  · linarith only [h17121, h17255, hlam]
                                                · linarith only [h17254, hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                rcases p17250_3 (m.d 0 3) (by simp) with h17261 | h17261
                                                · rcases p17250_3 (m.d 1 3) (by simp) with h17262 | h17262
                                                  · rcases p17250_3 (m.d 2 3) (by simp) with h17263 | h17263
                                                    · linarith only [h16917, h17263, hlam]
                                                    · linarith only [h17126, h17263, hlam]
                                                  · linarith only [h17122, h17262, hlam]
                                                · linarith only [h17261, hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h14396, h16915, h16922, h17118, h17119, h17125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17131_1, p17250_1]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h17118, h17126, h17129, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17153_1, p17250_1]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                rcases p17250_3 (m.d 0 3) (by simp) with h17271 | h17271
                                                · linarith only [h14396, h17271, hlam]
                                                · linarith only [h16920, h17271, hlam]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                rcases p17250_3 (m.d 0 3) (by simp) with h17274 | h17274
                                                · linarith only [h14396, h17274, hlam]
                                                · linarith only [h16921, h17274, hlam]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h16917, hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h17118, hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h16917, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p17250_1]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h0, h16917, h17129, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17250_1]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h16920, hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h17121, hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h17125, hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h17129, hlam, p17250_1]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h16921, hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h17122, hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h17126, hlam, p17250_0]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [h0, h16919, h17126, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17250_1]
                                              · have p17250_0 := h17250c.1
                                                have p17250_1 := h17250c.2.1
                                                have p17250_2 := h17250c.2.2.1
                                                have p17250_3 := h17250c.2.2.2
                                                linarith only [hlam, p17250_0]
                                        · linarith only [h17126, h17245, hlam]
                                      · linarith only [h17120, h17244, hlam]
                                    · linarith only [h16919, h17243, hlam]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h16918, hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h17119, hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h17125, hlam, p17153_1]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h17127, hlam, p17153_1]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h16919, hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h17120, hlam, p17153_0]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h17126, hlam, p17153_1]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [h16916, h17120, h17125, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p17131_1, p17153_1]
                                  · have p17153_0 := h17153c.1
                                    have p17153_1 := h17153c.2.1
                                    have p17153_2 := h17153c.2.2.1
                                    have p17153_3 := h17153c.2.2.2
                                    linarith only [hlam, p17153_0]
                            · linarith only [h16921, h17148, hlam]
                          · linarith only [h16919, h17147, hlam]
                        · linarith only [h16916, h17146, hlam]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        rcases p17131_3 (m.d 0 1) (by simp) with h17308 | h17308
                        · linarith only [h0, h17308, hlam]
                        · rcases p17131_3 (m.d 0 2) (by simp) with h17310 | h17310
                          · rcases p17131_3 (m.d 0 3) (by simp) with h17311 | h17311
                            · linarith only [h16917, h17311, hlam]
                            · linarith only [h14396, h17311, hlam]
                          · linarith only [h0, h17310, hlam]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [hlam, p17131_0]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        rcases p17131_3 (m.d 0 1) (by simp) with h17316 | h17316
                        · linarith only [h0, h17316, hlam]
                        · rcases p17131_3 (m.d 0 2) (by simp) with h17318 | h17318
                          · rcases p17131_3 (m.d 0 3) (by simp) with h17319 | h17319
                            · linarith only [h16917, h17319, hlam]
                            · rcases p17131_3 (m.d 0 4) (by simp) with h17321 | h17321
                              · linarith only [h16918, h17321, hlam]
                              · rcases p17131_3 (m.d 0 5) (by simp) with h17323 | h17323
                                · linarith only [h16919, h17323, hlam]
                                · rcases h2bigk with h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c | h17325c
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [hlam, p17325_0]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h0, hlam, p17325_1]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    rcases p17325_3 (m.d 0 2) (by simp) with h17328 | h17328
                                    · rcases p17325_3 (m.d 1 2) (by simp) with h17329 | h17329
                                      · rcases p17325_3 (m.d 2 3) (by simp) with h17330 | h17330
                                        · linarith only [h17330, hlam, p17325_0]
                                        · rcases p17325_3 (m.d 2 4) (by simp) with h17332 | h17332
                                          · linarith only [h16918, h17332, hlam]
                                          · rcases p17325_3 (m.d 2 5) (by simp) with h17334 | h17334
                                            · linarith only [h16919, h17334, hlam]
                                            · rcases h3bigk with h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c | h17336c
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [hlam, p17336_0]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h14396, hlam, p17336_1]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h0, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17131_1, p17336_1]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17131_1, p17336_1]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p17131_1, p17336_1]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h14396, h17118, hc01, hc12, hlam, hphi, p17336_1]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [hlam, p17336_0]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h17118, h17125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17336_1]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                rcases p17336_3 (m.d 0 3) (by simp) with h17345 | h17345
                                                · linarith only [h14396, h17345, hlam]
                                                · linarith only [h16920, h17345, hlam]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                rcases p17336_3 (m.d 0 3) (by simp) with h17348 | h17348
                                                · linarith only [h14396, h17348, hlam]
                                                · linarith only [h16921, h17348, hlam]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h16917, hlam, p17336_0]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h17118, hlam, p17336_0]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [hlam, p17336_0]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17325_1, p17336_1]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h0, h17129, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17325_1, p17336_1]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h16920, hlam, p17336_0]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h17121, hlam, p17336_0]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h17125, hlam, p17336_0]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [hlam, p17336_0]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h17129, hlam, p17336_1]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h16921, hlam, p17336_0]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h17122, hlam, p17336_0]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h17126, hlam, p17336_0]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [h0, h16921, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17131_1, p17336_1]
                                              · have p17336_0 := h17336c.1
                                                have p17336_1 := h17336c.2.1
                                                have p17336_2 := h17336c.2.2.1
                                                have p17336_3 := h17336c.2.2.2
                                                linarith only [hlam, p17336_0]
                                      · linarith only [h17118, h17329, hlam]
                                    · linarith only [h17328, hlam, p17325_0]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h14396, h16916, h17119, h17123, hlam, p17131_1, p17325_2]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h14396, h16916, h17120, hlam, p17131_1, p17325_2]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h14396, h16916, h17119, h17123, h17125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17131_1, p17325_1]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [hlam, p17325_0]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    rcases p17325_3 (m.d 0 2) (by simp) with h17372 | h17372
                                    · linarith only [h0, h17372, hlam]
                                    · linarith only [h16917, h17372, hlam]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h0, h14396, h16916, h17119, h17123, hlam, p17131_1, p17325_2]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h0, h14396, h16916, h17120, hlam, p17131_1, p17325_2]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h16917, hlam, p17325_0]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h17118, hlam, p17325_0]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [hlam, p17325_0]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h16917, h17125, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p17131_1, p17325_1]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h0, h16917, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p17131_1, p17325_1]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h16918, hlam, p17325_0]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h17119, hlam, p17325_0]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h17125, hlam, p17325_1]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [hlam, p17325_0]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h17127, hlam, p17325_1]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h16919, hlam, p17325_0]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h17120, hlam, p17325_0]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h17126, hlam, p17325_1]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [h0, h14396, h16916, h16919, h17125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17131_1, p17325_1]
                                  · have p17325_0 := h17325c.1
                                    have p17325_1 := h17325c.2.1
                                    have p17325_2 := h17325c.2.2.1
                                    have p17325_3 := h17325c.2.2.2
                                    linarith only [hlam, p17325_0]
                          · linarith only [h16917, h17318, hlam]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        rcases p17131_3 (m.d 0 1) (by simp) with h17393 | h17393
                        · linarith only [h0, h17393, hlam]
                        · linarith only [h16915, h17393, hlam]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        rcases p17131_3 (m.d 0 1) (by simp) with h17396 | h17396
                        · linarith only [h0, h17396, hlam]
                        · linarith only [h16916, h17396, hlam]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        rcases p17131_3 (m.d 0 1) (by simp) with h17399 | h17399
                        · linarith only [h14396, h17399, hlam]
                        · rcases p17131_3 (m.d 0 2) (by simp) with h17401 | h17401
                          · rcases p17131_3 (m.d 0 3) (by simp) with h17402 | h17402
                            · rcases p17131_3 (m.d 0 4) (by simp) with h17403 | h17403
                              · linarith only [h16920, h17403, hlam]
                              · rcases p17131_3 (m.d 0 5) (by simp) with h17405 | h17405
                                · linarith only [h16921, h17405, hlam]
                                · rcases h2bigk with h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c | h17407c
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [hlam, p17407_0]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h0, hlam, p17407_1]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    rcases p17407_3 (m.d 0 2) (by simp) with h17410 | h17410
                                    · rcases p17407_3 (m.d 1 2) (by simp) with h17411 | h17411
                                      · rcases p17407_3 (m.d 2 3) (by simp) with h17412 | h17412
                                        · linarith only [h17412, hlam, p17407_0]
                                        · rcases p17407_3 (m.d 2 4) (by simp) with h17414 | h17414
                                          · linarith only [h16918, h17414, hlam]
                                          · rcases p17407_3 (m.d 2 5) (by simp) with h17416 | h17416
                                            · linarith only [h16919, h17416, hlam]
                                            · rcases h3bigk with h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c | h17418c
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h14396, hlam, p17418_1]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h16917, hlam, p17407_2, p17418_1]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                rcases p17418_3 (m.d 0 3) (by simp) with h17422 | h17422
                                                · rcases p17418_3 (m.d 1 3) (by simp) with h17423 | h17423
                                                  · rcases p17418_3 (m.d 2 3) (by simp) with h17424 | h17424
                                                    · linarith only [h16917, h17424, hlam]
                                                    · linarith only [h17125, h17424, hlam]
                                                  · linarith only [h17121, h17423, hlam]
                                                · linarith only [h17422, hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                rcases p17418_3 (m.d 0 3) (by simp) with h17429 | h17429
                                                · rcases p17418_3 (m.d 1 3) (by simp) with h17430 | h17430
                                                  · rcases p17418_3 (m.d 2 3) (by simp) with h17431 | h17431
                                                    · linarith only [h16917, h17431, hlam]
                                                    · linarith only [h17126, h17431, hlam]
                                                  · linarith only [h17122, h17430, hlam]
                                                · linarith only [h17429, hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h17118, hc01, hc12, hlam, hphi, p17131_1, p17418_1]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h17118, h17126, h17129, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17418_1]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                rcases p17418_3 (m.d 0 3) (by simp) with h17439 | h17439
                                                · linarith only [h14396, h17439, hlam]
                                                · linarith only [h16920, h17439, hlam]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                rcases p17418_3 (m.d 0 3) (by simp) with h17442 | h17442
                                                · linarith only [h14396, h17442, hlam]
                                                · linarith only [h16921, h17442, hlam]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h16917, hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h17118, hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p17407_1, p17418_1]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h0, h17129, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17407_1, p17418_1]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h16920, hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h17121, hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h17125, hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h17129, hlam, p17418_1]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h16921, hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h17122, hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h17126, hlam, p17418_0]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [h0, h16919, h17126, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17418_1]
                                              · have p17418_0 := h17418c.1
                                                have p17418_1 := h17418c.2.1
                                                have p17418_2 := h17418c.2.2.1
                                                have p17418_3 := h17418c.2.2.2
                                                linarith only [hlam, p17418_0]
                                      · linarith only [h17118, h17411, hlam]
                                    · linarith only [h17410, hlam, p17407_0]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h16916, h16917, h17119, h17123, hlam, p17131_1, p17407_2]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h16916, h16917, h17120, hlam, p17131_1, p17407_2]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h16916, h16917, h17119, h17123, h17125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17131_1, p17407_1]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [hlam, p17407_0]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    rcases p17407_3 (m.d 0 2) (by simp) with h17466 | h17466
                                    · linarith only [h0, h17466, hlam]
                                    · linarith only [h16917, h17466, hlam]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h0, h16916, h16917, h17119, h17123, hlam, p17131_1, p17407_2]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h0, h16916, h16917, h17120, hlam, p17131_1, p17407_2]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h16917, hlam, p17407_0]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h17118, hlam, p17407_0]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [hlam, p17407_0]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    rcases p17407_3 (m.d 0 2) (by simp) with h17474 | h17474
                                    · rcases p17407_3 (m.d 1 2) (by simp) with h17475 | h17475
                                      · rcases p17407_3 (m.d 2 3) (by simp) with h17476 | h17476
                                        · rcases p17407_3 (m.d 2 4) (by simp) with h17477 | h17477
                                          · linarith only [h17125, h17477, hlam]
                                          · rcases p17407_3 (m.d 2 5) (by simp) with h17479 | h17479
                                            · linarith only [h17126, h17479, hlam]
                                            · linarith only [h17127, h17479, hlam]
                                        · linarith only [h17125, h17476, hlam]
                                      · linarith only [h17119, h17475, hlam]
                                    · linarith only [h16918, h17474, hlam]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    rcases p17407_3 (m.d 0 2) (by simp) with h17485 | h17485
                                    · rcases p17407_3 (m.d 1 2) (by simp) with h17486 | h17486
                                      · rcases p17407_3 (m.d 2 3) (by simp) with h17487 | h17487
                                        · rcases p17407_3 (m.d 2 4) (by simp) with h17488 | h17488
                                          · linarith only [h17125, h17488, hlam]
                                          · rcases p17407_3 (m.d 2 5) (by simp) with h17490 | h17490
                                            · linarith only [h17126, h17490, hlam]
                                            · rcases h3bigk with h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c | h17492c
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h14396, hlam, p17492_1]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h16917, hc02, hc25, hlam, hphi, ht0b, ht5b, p17407_1, p17492_1]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                rcases p17492_3 (m.d 0 3) (by simp) with h17496 | h17496
                                                · rcases p17492_3 (m.d 1 3) (by simp) with h17497 | h17497
                                                  · rcases p17492_3 (m.d 2 3) (by simp) with h17498 | h17498
                                                    · linarith only [h16917, h17498, hlam]
                                                    · linarith only [h17125, h17498, hlam]
                                                  · linarith only [h17121, h17497, hlam]
                                                · linarith only [h17496, hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                rcases p17492_3 (m.d 0 3) (by simp) with h17503 | h17503
                                                · rcases p17492_3 (m.d 1 3) (by simp) with h17504 | h17504
                                                  · rcases p17492_3 (m.d 2 3) (by simp) with h17505 | h17505
                                                    · linarith only [h16917, h17505, hlam]
                                                    · linarith only [h17126, h17505, hlam]
                                                  · linarith only [h17122, h17504, hlam]
                                                · linarith only [h17503, hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h16916, h17118, h17119, h17123, h17125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17131_1, p17492_1]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h17118, h17125, h17127, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17407_1, p17492_1]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                rcases p17492_3 (m.d 0 3) (by simp) with h17513 | h17513
                                                · linarith only [h14396, h17513, hlam]
                                                · linarith only [h16920, h17513, hlam]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                rcases p17492_3 (m.d 0 3) (by simp) with h17516 | h17516
                                                · linarith only [h14396, h17516, hlam]
                                                · linarith only [h16921, h17516, hlam]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h16917, hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h17118, hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h16917, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p17492_1]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h0, h16917, h17129, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17492_1]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h16920, hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h17121, hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h17125, hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h17129, hlam, p17492_1]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h16921, hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h17122, hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h17126, hlam, p17492_0]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [h16921, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p17492_1]
                                              · have p17492_0 := h17492c.1
                                                have p17492_1 := h17492c.2.1
                                                have p17492_2 := h17492c.2.2.1
                                                have p17492_3 := h17492c.2.2.2
                                                linarith only [hlam, p17492_0]
                                        · linarith only [h17126, h17487, hlam]
                                      · linarith only [h17120, h17486, hlam]
                                    · linarith only [h16919, h17485, hlam]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h16918, hlam, p17407_0]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h17119, hlam, p17407_0]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h17125, hlam, p17407_1]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [hlam, p17407_0]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h17127, hlam, p17407_1]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h16919, hlam, p17407_0]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h17120, hlam, p17407_0]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h17126, hlam, p17407_1]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [h14396, h16916, h16919, h17118, h17125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17131_1, p17407_1]
                                  · have p17407_0 := h17407c.1
                                    have p17407_1 := h17407c.2.1
                                    have p17407_2 := h17407c.2.2.1
                                    have p17407_3 := h17407c.2.2.2
                                    linarith only [hlam, p17407_0]
                            · linarith only [h14396, h17402, hlam]
                          · linarith only [h0, h17401, hlam]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [h16917, hlam, p17131_1]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [hlam, p17131_0]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        rcases p17131_3 (m.d 0 1) (by simp) with h17551 | h17551
                        · linarith only [h14396, h17551, hlam]
                        · linarith only [h16915, h17551, hlam]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        rcases p17131_3 (m.d 0 1) (by simp) with h17554 | h17554
                        · linarith only [h14396, h17554, hlam]
                        · linarith only [h16916, h17554, hlam]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [h16915, hlam, p17131_0]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [h16918, hlam, p17131_0]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [h16920, hlam, p17131_0]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [hlam, p17131_0]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [h16922, hlam, p17131_0]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [h16916, hlam, p17131_0]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [h16919, hlam, p17131_1]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [h16921, hlam, p17131_0]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        rcases p17131_3 (m.d 0 1) (by simp) with h17565 | h17565
                        · rcases p17131_3 (m.d 0 2) (by simp) with h17566 | h17566
                          · rcases p17131_3 (m.d 0 3) (by simp) with h17567 | h17567
                            · rcases p17131_3 (m.d 0 4) (by simp) with h17568 | h17568
                              · linarith only [h16922, h17568, hlam]
                              · rcases p17131_3 (m.d 0 5) (by simp) with h17570 | h17570
                                · rcases h2bigk with h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c | h17571c
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h0, hlam, p17571_1]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    rcases p17571_3 (m.d 0 2) (by simp) with h17574 | h17574
                                    · rcases p17571_3 (m.d 1 2) (by simp) with h17575 | h17575
                                      · rcases p17571_3 (m.d 2 3) (by simp) with h17576 | h17576
                                        · linarith only [h17576, hlam, p17571_0]
                                        · rcases p17571_3 (m.d 2 4) (by simp) with h17578 | h17578
                                          · linarith only [h16918, h17578, hlam]
                                          · rcases p17571_3 (m.d 2 5) (by simp) with h17580 | h17580
                                            · linarith only [h16919, h17580, hlam]
                                            · rcases h3bigk with h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c | h17582c
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h14396, hlam, p17582_1]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h14396, h17118, h17126, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p17582_1]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                rcases p17582_3 (m.d 0 3) (by simp) with h17586 | h17586
                                                · rcases p17582_3 (m.d 1 3) (by simp) with h17587 | h17587
                                                  · rcases p17582_3 (m.d 2 3) (by simp) with h17588 | h17588
                                                    · linarith only [h16917, h17588, hlam]
                                                    · linarith only [h17125, h17588, hlam]
                                                  · linarith only [h17121, h17587, hlam]
                                                · linarith only [h17586, hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                rcases p17582_3 (m.d 0 3) (by simp) with h17593 | h17593
                                                · rcases p17582_3 (m.d 1 3) (by simp) with h17594 | h17594
                                                  · rcases p17582_3 (m.d 2 3) (by simp) with h17595 | h17595
                                                    · linarith only [h16917, h17595, hlam]
                                                    · linarith only [h17126, h17595, hlam]
                                                  · linarith only [h17122, h17594, hlam]
                                                · linarith only [h17593, hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h14396, h17118, hc01, hc12, hlam, hphi, p17582_1]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h17118, h17125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17582_1]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                rcases p17582_3 (m.d 0 3) (by simp) with h17603 | h17603
                                                · linarith only [h14396, h17603, hlam]
                                                · linarith only [h16920, h17603, hlam]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                rcases p17582_3 (m.d 0 3) (by simp) with h17606 | h17606
                                                · linarith only [h14396, h17606, hlam]
                                                · linarith only [h16921, h17606, hlam]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h16917, hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h17118, hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17571_1, p17582_1]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h0, h17129, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17571_1, p17582_1]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h16920, hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h17121, hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h17125, hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h17129, hlam, p17582_1]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h16921, hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h17122, hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h17126, hlam, p17582_0]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [h0, h16919, h17126, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17582_1]
                                              · have p17582_0 := h17582c.1
                                                have p17582_1 := h17582c.2.1
                                                have p17582_2 := h17582c.2.2.1
                                                have p17582_3 := h17582c.2.2.2
                                                linarith only [hlam, p17582_0]
                                      · linarith only [h17118, h17575, hlam]
                                    · linarith only [h17574, hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    rcases p17571_3 (m.d 0 2) (by simp) with h17626 | h17626
                                    · rcases p17571_3 (m.d 1 2) (by simp) with h17627 | h17627
                                      · rcases p17571_3 (m.d 2 3) (by simp) with h17628 | h17628
                                        · linarith only [h16917, h17628, hlam]
                                        · linarith only [h17125, h17628, hlam]
                                      · linarith only [h17119, h17627, hlam]
                                    · linarith only [h17626, hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    rcases p17571_3 (m.d 0 2) (by simp) with h17633 | h17633
                                    · rcases p17571_3 (m.d 1 2) (by simp) with h17634 | h17634
                                      · rcases p17571_3 (m.d 2 3) (by simp) with h17635 | h17635
                                        · linarith only [h16917, h17635, hlam]
                                        · linarith only [h17126, h17635, hlam]
                                      · linarith only [h17120, h17634, hlam]
                                    · linarith only [h17633, hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h0, h16915, h16916, h17119, h17125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17131_1, p17571_1]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    rcases p17571_3 (m.d 0 2) (by simp) with h17642 | h17642
                                    · linarith only [h0, h17642, hlam]
                                    · linarith only [h16917, h17642, hlam]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h0, h16915, h16916, h17119, hlam, p17131_1, p17571_2]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    rcases p17571_3 (m.d 0 2) (by simp) with h17646 | h17646
                                    · linarith only [h0, h17646, hlam]
                                    · linarith only [h16919, h17646, hlam]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h16917, hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h17118, hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    rcases p17571_3 (m.d 0 2) (by simp) with h17652 | h17652
                                    · rcases p17571_3 (m.d 1 2) (by simp) with h17653 | h17653
                                      · rcases p17571_3 (m.d 2 3) (by simp) with h17654 | h17654
                                        · rcases p17571_3 (m.d 2 4) (by simp) with h17655 | h17655
                                          · linarith only [h17125, h17655, hlam]
                                          · rcases p17571_3 (m.d 2 5) (by simp) with h17657 | h17657
                                            · linarith only [h17126, h17657, hlam]
                                            · linarith only [h17127, h17657, hlam]
                                        · linarith only [h17125, h17654, hlam]
                                      · linarith only [h17119, h17653, hlam]
                                    · linarith only [h16918, h17652, hlam]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    rcases p17571_3 (m.d 0 2) (by simp) with h17663 | h17663
                                    · rcases p17571_3 (m.d 1 2) (by simp) with h17664 | h17664
                                      · rcases p17571_3 (m.d 2 3) (by simp) with h17665 | h17665
                                        · rcases p17571_3 (m.d 2 4) (by simp) with h17666 | h17666
                                          · linarith only [h17125, h17666, hlam]
                                          · rcases p17571_3 (m.d 2 5) (by simp) with h17668 | h17668
                                            · linarith only [h17126, h17668, hlam]
                                            · rcases h3bigk with h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c | h17670c
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h14396, hlam, p17670_1]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [hc03, hc25, hlam, hphi, ht0b, ht5b, p17571_1, p17670_1]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                rcases p17670_3 (m.d 0 3) (by simp) with h17674 | h17674
                                                · rcases p17670_3 (m.d 1 3) (by simp) with h17675 | h17675
                                                  · rcases p17670_3 (m.d 2 3) (by simp) with h17676 | h17676
                                                    · linarith only [h16917, h17676, hlam]
                                                    · linarith only [h17125, h17676, hlam]
                                                  · linarith only [h17121, h17675, hlam]
                                                · linarith only [h17674, hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                rcases p17670_3 (m.d 0 3) (by simp) with h17681 | h17681
                                                · rcases p17670_3 (m.d 1 3) (by simp) with h17682 | h17682
                                                  · rcases p17670_3 (m.d 2 3) (by simp) with h17683 | h17683
                                                    · linarith only [h16917, h17683, hlam]
                                                    · linarith only [h17126, h17683, hlam]
                                                  · linarith only [h17122, h17682, hlam]
                                                · linarith only [h17681, hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h14396, h16915, h16916, h17118, h17119, h17125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17131_1, p17670_1]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h17118, h17125, h17127, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17571_1, p17670_1]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                rcases p17670_3 (m.d 0 3) (by simp) with h17691 | h17691
                                                · linarith only [h14396, h17691, hlam]
                                                · linarith only [h16920, h17691, hlam]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                rcases p17670_3 (m.d 0 3) (by simp) with h17694 | h17694
                                                · linarith only [h14396, h17694, hlam]
                                                · linarith only [h16921, h17694, hlam]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h16917, hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h17118, hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h0, h16917, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17670_1]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h0, h16917, h17129, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17670_1]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h16920, hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h17121, hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h17125, hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h17129, hlam, p17670_1]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h16921, hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h17122, hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h17126, hlam, p17670_0]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [h16921, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p17670_1]
                                              · have p17670_0 := h17670c.1
                                                have p17670_1 := h17670c.2.1
                                                have p17670_2 := h17670c.2.2.1
                                                have p17670_3 := h17670c.2.2.2
                                                linarith only [hlam, p17670_0]
                                        · linarith only [h17126, h17665, hlam]
                                      · linarith only [h17120, h17664, hlam]
                                    · linarith only [h16919, h17663, hlam]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h16918, hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h17119, hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h17125, hlam, p17571_1]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h17127, hlam, p17571_1]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h16919, hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h17120, hlam, p17571_0]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h17126, hlam, p17571_1]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [h0, h16916, h17120, h17125, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17571_1]
                                  · have p17571_0 := h17571c.1
                                    have p17571_1 := h17571c.2.1
                                    have p17571_2 := h17571c.2.2.1
                                    have p17571_3 := h17571c.2.2.2
                                    linarith only [hlam, p17571_0]
                                · linarith only [h16922, h17570, hlam]
                            · linarith only [h16920, h17567, hlam]
                          · linarith only [h16918, h17566, hlam]
                        · linarith only [h16915, h17565, hlam]
                      · have p17131_0 := h17131c.1
                        have p17131_1 := h17131c.2.1
                        have p17131_2 := h17131c.2.2.1
                        have p17131_3 := h17131c.2.2.2
                        linarith only [hlam, p17131_0]
                · linarith only [h14396, h16916, h17118, h17122, h17125, h17126, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h17731 | h17731
                · linarith only [h14396, h16915, h17118, h17121, h17125, h17731, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h17733 | h17733
                  · linarith only [h14396, h16916, h16922, h17118, h17121, h17123, h17125, h17733, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17735 | h17735
                    · linarith only [h16915, h16922, h17121, h17735, hlam]
                    · rcases h0bigk with h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c | h17737c
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [hlam, p17737_0]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h0, hlam, p17737_1]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h14396, hlam, p17737_0]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h14396, h16915, h17118, h17121, h17125, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17737_1]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h14396, h16915, h16922, h17118, h17121, h17125, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17737_1]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h0, h16915, h17121, h17125, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17737_1]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [hlam, p17737_0]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h0, h14396, h16915, h17121, h17125, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17737_1]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        rcases p17737_3 (m.d 0 1) (by simp) with h17746 | h17746
                        · linarith only [h0, h17746, hlam]
                        · linarith only [h16915, h17746, hlam]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        rcases p17737_3 (m.d 0 1) (by simp) with h17749 | h17749
                        · linarith only [h0, h17749, hlam]
                        · linarith only [h16916, h17749, hlam]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h16916, h17121, h17123, h17125, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17737_1]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h16917, hlam, p17737_1]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [hlam, p17737_0]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        rcases p17737_3 (m.d 0 1) (by simp) with h17755 | h17755
                        · linarith only [h14396, h17755, hlam]
                        · linarith only [h16915, h17755, hlam]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        rcases p17737_3 (m.d 0 1) (by simp) with h17758 | h17758
                        · linarith only [h14396, h17758, hlam]
                        · linarith only [h16916, h17758, hlam]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h16915, hlam, p17737_0]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h16918, hlam, p17737_0]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h16920, hlam, p17737_0]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [hlam, p17737_0]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h16922, hlam, p17737_0]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h16916, hlam, p17737_0]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h16919, hlam, p17737_1]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h16921, hlam, p17737_0]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [h0, h16915, h16916, h17121, h17125, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17737_1]
                      · have p17737_0 := h17737c.1
                        have p17737_1 := h17737c.2.1
                        have p17737_2 := h17737c.2.2.1
                        have p17737_3 := h17737c.2.2.2
                        linarith only [hlam, p17737_0]
          · linarith only [h14396, h16921, h17122, hlam]
        · linarith only [h14396, h16920, h17121, hlam]
      · linarith only [h0, h16919, h17120, hlam]
    · linarith only [h0, h16918, h17119, hlam]
  · linarith only [h0, h16917, h17118, hlam]

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16917 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h16918 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h16919 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h16920 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h16921 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h14396 := hg14396
  rcases m.htr 0 4 5 (by decide) (by decide) with h16922 | h16922
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916 h16917 h16918 h16919 h16920 h16921 h16922
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916 h16917 h16918 h16919 h16920 h16921 h16922

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16917 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h16918 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h16919 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h16920 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h16921 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h14396 := hg14396
  linarith only [h14396, h16916, h16921, hlam]

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16917 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h16918 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h16919 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h16920 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h14396 := hg14396
  rcases m.htr 0 3 5 (by decide) (by decide) with h16921 | h16921
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916 h16917 h16918 h16919 h16920 h16921
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916 h16917 h16918 h16919 h16920 h16921

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16917 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h16918 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h16919 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h16920 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h14396 := hg14396
  linarith only [h14396, h16915, h16920, hlam]

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16917 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h16918 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h16919 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h14396 := hg14396
  rcases m.htr 0 3 4 (by decide) (by decide) with h16920 | h16920
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916 h16917 h16918 h16919 h16920
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916 h16917 h16918 h16919 h16920

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16917 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h16918 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h16919 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h14396 := hg14396
  linarith only [h0, h16916, h16919, hlam]

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16917 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h16918 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h14396 := hg14396
  rcases m.htr 0 2 5 (by decide) (by decide) with h16919 | h16919
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916 h16917 h16918 h16919
  · exact r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 h16915 h16916 h16917 h16918 h16919

set_option maxHeartbeats 23648000 in
set_option maxHeartbeats 23648000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s16_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16915 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16916 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16917 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h16918 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h14396 := hg14396
  linarith only [h14396, h16915, h16917, h16918, hlam]

end R2N4
