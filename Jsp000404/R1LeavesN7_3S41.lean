import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S40

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14800 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14801 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14802 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14803 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14804 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h14805 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h15173 | h15173
  · rcases m.htr 0 4 5 (by decide) (by decide) with h15174 | h15174
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15175 | h15175
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15176 | h15176
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15177 | h15177
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15178 | h15178
            · linarith only [h0, h14799, h14805, h15178, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15180 | h15180
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15181 | h15181
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15182 | h15182
                  · linarith only [h14799, h14805, h15175, h15182, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15184 | h15184
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15185 | h15185
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15186 | h15186
                        · rcases h1bigk with h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c | h15187c
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [hlam, p15187_0]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h0, hlam, p15187_0]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h0, h15175, h15184, h15186, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15187_1]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h0, h15175, h15178, h15184, h15186, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15187_1]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            rcases p15187_3 (m.d 0 1) (by simp) with h15192 | h15192
                            · rcases p15187_3 (m.d 1 2) (by simp) with h15193 | h15193
                              · rcases p15187_3 (m.d 1 3) (by simp) with h15194 | h15194
                                · linarith only [h14799, h15194, hlam]
                                · linarith only [h15180, h15194, hlam]
                              · linarith only [h15177, h15193, hlam]
                            · linarith only [h15192, hlam, p15187_0]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h14799, h15175, h15184, h15186, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15187_1]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [hlam, p15187_0]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            rcases p15187_3 (m.d 0 1) (by simp) with h15201 | h15201
                            · linarith only [h0, h15201, hlam]
                            · linarith only [h14799, h15201, hlam]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            rcases p15187_3 (m.d 0 1) (by simp) with h15204 | h15204
                            · linarith only [h0, h15204, hlam]
                            · linarith only [h14800, h15204, hlam]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            rcases p15187_3 (m.d 0 1) (by simp) with h15207 | h15207
                            · linarith only [h0, h15207, hlam]
                            · linarith only [h14801, h15207, hlam]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h14799, hlam, p15187_0]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h15175, hlam, p15187_1]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [hlam, p15187_0]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h15178, hlam, p15187_1]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h0, h14800, h15178, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p15187_1]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h14800, hlam, p15187_0]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h15176, hlam, p15187_1]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h14800, h15175, h15184, hc01, hc35, hlam, hphi, ht0b, ht5b, p15187_1]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [hlam, p15187_0]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h0, h14800, h15180, h15186, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15187_1]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h14801, hlam, p15187_0]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h15177, hlam, p15187_1]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h15180, hlam, p15187_0]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [h15181, hlam, p15187_0]
                          · have p15187_0 := h15187c.1
                            have p15187_1 := h15187c.2.1
                            have p15187_2 := h15187c.2.2.1
                            have p15187_3 := h15187c.2.2.2
                            linarith only [hlam, p15187_0]
                        · linarith only [h14799, h14805, h15174, h15175, h15184, h15186, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h14800, h15181, h15185, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h14805, h15173, h15184, hc23, hc34, hlam, hphi]
                · linarith only [h0, h14800, h15174, h15178, h15180, h15181, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h14805, h15173, h15180, hc13, hc34, hlam, hphi]
          · linarith only [h0, h14804, h15177, hlam]
        · linarith only [h0, h14803, h15176, hlam]
      · linarith only [h0, h14802, h15175, hlam]
    · linarith only [h14805, h15173, h15174, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h15234 | h15234
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15235 | h15235
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15236 | h15236
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15237 | h15237
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15238 | h15238
            · linarith only [h0, h14799, h14805, h15238, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15240 | h15240
              · linarith only [h14799, h15173, h15240, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15242 | h15242
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15243 | h15243
                  · linarith only [h14802, h14805, h15243, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15245 | h15245
                    · linarith only [h14799, h15173, h15235, h15245, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15247 | h15247
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15248 | h15248
                        · rcases h1bigk with h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c | h15249c
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [hlam, p15249_0]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h0, hlam, p15249_0]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            rcases p15249_3 (m.d 0 1) (by simp) with h15252 | h15252
                            · rcases p15249_3 (m.d 1 2) (by simp) with h15253 | h15253
                              · rcases p15249_3 (m.d 1 3) (by simp) with h15254 | h15254
                                · linarith only [h15254, hlam, p15249_0]
                                · rcases p15249_3 (m.d 1 4) (by simp) with h15256 | h15256
                                  · linarith only [h14800, h15256, hlam]
                                  · linarith only [h15238, h15256, hlam]
                              · linarith only [h15235, h15253, hlam]
                            · linarith only [h15252, hlam, p15249_0]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h0, h15242, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15249_1]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            rcases p15249_3 (m.d 0 1) (by simp) with h15262 | h15262
                            · rcases p15249_3 (m.d 1 2) (by simp) with h15263 | h15263
                              · rcases p15249_3 (m.d 1 3) (by simp) with h15264 | h15264
                                · linarith only [h14799, h15264, hlam]
                                · rcases p15249_3 (m.d 1 4) (by simp) with h15266 | h15266
                                  · linarith only [h14800, h15266, hlam]
                                  · linarith only [h15242, h15266, hlam]
                              · linarith only [h15237, h15263, hlam]
                            · linarith only [h15262, hlam, p15249_0]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h14800, h15236, h15247, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p15249_1]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [hlam, p15249_0]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            rcases p15249_3 (m.d 0 1) (by simp) with h15273 | h15273
                            · linarith only [h0, h15273, hlam]
                            · linarith only [h14799, h15273, hlam]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            rcases p15249_3 (m.d 0 1) (by simp) with h15276 | h15276
                            · linarith only [h0, h15276, hlam]
                            · linarith only [h14800, h15276, hlam]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            rcases p15249_3 (m.d 0 1) (by simp) with h15279 | h15279
                            · linarith only [h0, h15279, hlam]
                            · linarith only [h14801, h15279, hlam]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h14799, hlam, p15249_0]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h15235, hlam, p15249_1]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [hlam, p15249_0]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h15238, hlam, p15249_1]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h15240, hlam, p15249_1]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h14800, hlam, p15249_0]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h15236, hlam, p15249_1]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h0, h14800, h15235, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15249_1]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [hlam, p15249_0]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h0, h14800, h15235, h15240, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15249_1]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h14801, hlam, p15249_0]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h15237, hlam, p15249_1]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h0, h14801, h15235, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15249_1]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [h15242, hlam, p15249_0]
                          · have p15249_0 := h15249c.1
                            have p15249_1 := h15249c.2.1
                            have p15249_2 := h15249c.2.2.1
                            have p15249_3 := h15249c.2.2.2
                            linarith only [hlam, p15249_0]
                        · linarith only [h14805, h15234, h15248, hlam]
                      · linarith only [h0, h14800, h15242, h15247, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15299 | h15299
                  · linarith only [h0, h14799, h14805, h15234, h15235, h15242, h15299, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15301 | h15301
                    · linarith only [h15173, h15234, h15235, h15238, h15242, h15301, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15303 | h15303
                      · linarith only [h15236, h15242, h15303, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15305 | h15305
                        · rcases h1bigk with h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c | h15306c
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [hlam, p15306_0]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h0, hlam, p15306_0]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            rcases p15306_3 (m.d 0 1) (by simp) with h15309 | h15309
                            · rcases p15306_3 (m.d 1 2) (by simp) with h15310 | h15310
                              · rcases p15306_3 (m.d 1 3) (by simp) with h15311 | h15311
                                · linarith only [h15311, hlam, p15306_0]
                                · rcases p15306_3 (m.d 1 4) (by simp) with h15313 | h15313
                                  · linarith only [h14800, h15313, hlam]
                                  · linarith only [h15238, h15313, hlam]
                              · linarith only [h15235, h15310, hlam]
                            · linarith only [h15309, hlam, p15306_0]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            rcases p15306_3 (m.d 0 1) (by simp) with h15318 | h15318
                            · rcases p15306_3 (m.d 1 2) (by simp) with h15319 | h15319
                              · rcases p15306_3 (m.d 1 3) (by simp) with h15320 | h15320
                                · linarith only [h14799, h15320, hlam]
                                · rcases p15306_3 (m.d 1 4) (by simp) with h15322 | h15322
                                  · linarith only [h15322, hlam, p15306_0]
                                  · rcases p15306_3 (m.d 1 5) (by simp) with h15324 | h15324
                                    · linarith only [h14801, h15324, hlam]
                                    · linarith only [h15242, h15324, hlam]
                              · linarith only [h15236, h15319, hlam]
                            · linarith only [h15318, hlam, p15306_0]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            rcases p15306_3 (m.d 0 1) (by simp) with h15329 | h15329
                            · rcases p15306_3 (m.d 1 2) (by simp) with h15330 | h15330
                              · rcases p15306_3 (m.d 1 3) (by simp) with h15331 | h15331
                                · linarith only [h14799, h15331, hlam]
                                · rcases p15306_3 (m.d 1 4) (by simp) with h15333 | h15333
                                  · linarith only [h14800, h15333, hlam]
                                  · rcases p15306_3 (m.d 1 5) (by simp) with h15335 | h15335
                                    · linarith only [h15335, hlam, p15306_0]
                                    · rcases h3bigk with h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c | h15337c
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h14805, h15235, hc23, hc34, hlam, hphi, p15337_1]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h14805, hc23, hc34, hlam, hphi, p15337_1]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h14805, hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h15173, hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h14799, hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h0, h14799, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15337_1]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h15238, hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h15240, hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h14802, hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h15235, hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h15299, hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h15301, hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        rcases p15337_3 (m.d 0 3) (by simp) with h15353 | h15353
                                        · linarith only [h15353, hlam, p15337_0]
                                        · rcases p15337_3 (m.d 1 3) (by simp) with h15355 | h15355
                                          · linarith only [h15238, h15355, hlam]
                                          · rcases p15337_3 (m.d 2 3) (by simp) with h15357 | h15357
                                            · linarith only [h15299, h15357, hlam]
                                            · rcases p15337_3 (m.d 3 4) (by simp) with h15359 | h15359
                                              · rcases p15337_3 (m.d 3 5) (by simp) with h15360 | h15360
                                                · linarith only [h15305, h15360, hlam]
                                                · linarith only [h15173, h15360, hlam]
                                              · linarith only [h15359, hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        rcases p15337_3 (m.d 0 3) (by simp) with h15364 | h15364
                                        · linarith only [h14805, h15364, hlam]
                                        · linarith only [h14799, h15364, hlam]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        rcases p15337_3 (m.d 0 3) (by simp) with h15367 | h15367
                                        · linarith only [h14805, h15367, hlam]
                                        · linarith only [h14802, h15367, hlam]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h15173, hc03, hc34, hlam, hphi, p15337_1]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        rcases p15337_3 (m.d 0 3) (by simp) with h15372 | h15372
                                        · linarith only [h15372, hlam, p15337_0]
                                        · rcases p15337_3 (m.d 1 3) (by simp) with h15374 | h15374
                                          · linarith only [h15240, h15374, hlam]
                                          · rcases p15337_3 (m.d 2 3) (by simp) with h15376 | h15376
                                            · linarith only [h15301, h15376, hlam]
                                            · rcases p15337_3 (m.d 3 4) (by simp) with h15378 | h15378
                                              · rcases p15337_3 (m.d 3 5) (by simp) with h15379 | h15379
                                                · rcases h5bigk with h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c | h15380c
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [hlam, p15380_0]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h0, h14801, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h0, h14801, h15303, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h15173, hlam, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h0, h14800, h15234, h15242, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h14801, hlam, p15380_0]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [hlam, p15380_0]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h0, h15303, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15306_1, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h15240, hlam, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h15242, hlam, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h14804, hlam, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h15237, hlam, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [hlam, p15380_0]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h15301, hlam, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h15303, hlam, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h14799, h15173, h15235, hc23, hc35, hlam, hphi, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h15235, h15240, hc23, hc35, hlam, hphi, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h15299, h15303, hc23, hc35, hlam, hphi, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [hlam, p15380_0]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h15235, h15238, h15242, h15305, hc23, hc34, hlam, hphi, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h15234, hlam, p15380_0]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h15235, h15238, h15242, hc23, hc45, hlam, hphi, ht34, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h0, h14800, h15234, h15299, h15303, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15380_1]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [h15305, hlam, p15380_0]
                                                  · have p15380_0 := h15380c.1
                                                    have p15380_1 := h15380c.2.1
                                                    have p15380_2 := h15380c.2.2.1
                                                    have p15380_3 := h15380c.2.2.2
                                                    linarith only [hlam, p15380_0]
                                                · linarith only [h15379, hlam, p15337_0]
                                              · linarith only [h14805, h15378, hlam]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        rcases p15337_3 (m.d 0 3) (by simp) with h15408 | h15408
                                        · linarith only [h15173, h15408, hlam]
                                        · linarith only [h14799, h15408, hlam]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        rcases p15337_3 (m.d 0 3) (by simp) with h15411 | h15411
                                        · linarith only [h15173, h15411, hlam]
                                        · linarith only [h14802, h15411, hlam]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [h15305, hlam, p15337_0]
                                      · have p15337_0 := h15337c.1
                                        have p15337_1 := h15337c.2.1
                                        have p15337_2 := h15337c.2.2.1
                                        have p15337_3 := h15337c.2.2.2
                                        linarith only [hlam, p15337_0]
                              · linarith only [h15237, h15330, hlam]
                            · linarith only [h15329, hlam, p15306_0]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h14800, h15234, h15235, h15238, h15242, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15306_1]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [hlam, p15306_0]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h0, h14800, h15234, h15238, h15242, hlam, p15306_2]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h0, h14800, h15234, h15242, hlam, p15306_2]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            rcases p15306_3 (m.d 0 1) (by simp) with h15422 | h15422
                            · linarith only [h0, h15422, hlam]
                            · linarith only [h14801, h15422, hlam]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h14799, hlam, p15306_0]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h15235, hlam, p15306_1]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [hlam, p15306_0]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h15238, hlam, p15306_1]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h15240, hlam, p15306_1]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h14800, hlam, p15306_0]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h15236, hlam, p15306_1]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h0, h14800, h15234, h15242, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15306_1]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [hlam, p15306_0]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h15242, hlam, p15306_1]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h14801, hlam, p15306_0]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h15237, hlam, p15306_1]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h0, h14801, h15235, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15306_1]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [h0, h14800, h15234, h15242, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p15306_1]
                          · have p15306_0 := h15306c.1
                            have p15306_1 := h15306c.2.1
                            have p15306_2 := h15306c.2.2.1
                            have p15306_3 := h15306c.2.2.2
                            linarith only [hlam, p15306_0]
                        · linarith only [h0, h14799, h14800, h14805, h15234, h15235, h15305, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h14804, h15237, hlam]
        · linarith only [h0, h14803, h15236, hlam]
      · linarith only [h0, h14802, h15235, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15444 | h15444
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15445 | h15445
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15446 | h15446
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15447 | h15447
            · linarith only [h14799, h14805, h15447, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15449 | h15449
              · linarith only [h14799, h15173, h15449, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15451 | h15451
                · linarith only [h0, h14800, h14805, h15234, h15451, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15453 | h15453
                  · linarith only [h14799, h14805, h15444, h15453, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15455 | h15455
                    · linarith only [h14799, h15173, h15444, h15455, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15457 | h15457
                      · linarith only [h0, h14799, h14800, h14805, h15234, h15444, h15445, h15457, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15459 | h15459
                        · rcases h1bigk with h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c | h15460c
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [hlam, p15460_0]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h0, hlam, p15460_0]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            rcases p15460_3 (m.d 0 1) (by simp) with h15463 | h15463
                            · rcases p15460_3 (m.d 1 2) (by simp) with h15464 | h15464
                              · rcases p15460_3 (m.d 1 3) (by simp) with h15465 | h15465
                                · linarith only [h15465, hlam, p15460_0]
                                · rcases p15460_3 (m.d 1 4) (by simp) with h15467 | h15467
                                  · linarith only [h14800, h15467, hlam]
                                  · linarith only [h15447, h15467, hlam]
                              · linarith only [h15444, h15464, hlam]
                            · linarith only [h15463, hlam, p15460_0]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            rcases p15460_3 (m.d 0 1) (by simp) with h15472 | h15472
                            · rcases p15460_3 (m.d 1 2) (by simp) with h15473 | h15473
                              · rcases p15460_3 (m.d 1 3) (by simp) with h15474 | h15474
                                · linarith only [h14799, h15474, hlam]
                                · rcases p15460_3 (m.d 1 4) (by simp) with h15476 | h15476
                                  · linarith only [h15476, hlam, p15460_0]
                                  · rcases p15460_3 (m.d 1 5) (by simp) with h15478 | h15478
                                    · linarith only [h14801, h15478, hlam]
                                    · linarith only [h15451, h15478, hlam]
                              · linarith only [h15445, h15473, hlam]
                            · linarith only [h15472, hlam, p15460_0]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            rcases p15460_3 (m.d 0 1) (by simp) with h15483 | h15483
                            · rcases p15460_3 (m.d 1 2) (by simp) with h15484 | h15484
                              · rcases p15460_3 (m.d 1 3) (by simp) with h15485 | h15485
                                · linarith only [h14799, h15485, hlam]
                                · rcases p15460_3 (m.d 1 4) (by simp) with h15487 | h15487
                                  · linarith only [h14800, h15487, hlam]
                                  · rcases p15460_3 (m.d 1 5) (by simp) with h15489 | h15489
                                    · linarith only [h15489, hlam, p15460_0]
                                    · rcases h3bigk with h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c | h15491c
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h14805, h15444, hc23, hc34, hlam, hphi, p15491_1]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h14805, hc23, hc34, hlam, hphi, p15491_1]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h14805, hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h15173, hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h14799, hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h0, h14799, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15491_1]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h15447, hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h15449, hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h14802, hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h15444, hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h15453, hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h15455, hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        rcases p15491_3 (m.d 0 3) (by simp) with h15507 | h15507
                                        · linarith only [h15507, hlam, p15491_0]
                                        · rcases p15491_3 (m.d 1 3) (by simp) with h15509 | h15509
                                          · linarith only [h15447, h15509, hlam]
                                          · rcases p15491_3 (m.d 2 3) (by simp) with h15511 | h15511
                                            · linarith only [h15453, h15511, hlam]
                                            · rcases p15491_3 (m.d 3 4) (by simp) with h15513 | h15513
                                              · rcases p15491_3 (m.d 3 5) (by simp) with h15514 | h15514
                                                · linarith only [h15459, h15514, hlam]
                                                · linarith only [h15173, h15514, hlam]
                                              · linarith only [h15513, hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        rcases p15491_3 (m.d 0 3) (by simp) with h15518 | h15518
                                        · linarith only [h14805, h15518, hlam]
                                        · linarith only [h14799, h15518, hlam]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        rcases p15491_3 (m.d 0 3) (by simp) with h15521 | h15521
                                        · linarith only [h14805, h15521, hlam]
                                        · linarith only [h14802, h15521, hlam]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h14805, h15234, h15459, hc03, hc34, hlam, hphi, p15491_1]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        rcases p15491_3 (m.d 0 3) (by simp) with h15526 | h15526
                                        · linarith only [h15526, hlam, p15491_0]
                                        · rcases p15491_3 (m.d 1 3) (by simp) with h15528 | h15528
                                          · linarith only [h15449, h15528, hlam]
                                          · rcases p15491_3 (m.d 2 3) (by simp) with h15530 | h15530
                                            · linarith only [h15455, h15530, hlam]
                                            · rcases p15491_3 (m.d 3 4) (by simp) with h15532 | h15532
                                              · rcases p15491_3 (m.d 3 5) (by simp) with h15533 | h15533
                                                · rcases h5bigk with h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c | h15534c
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [hlam, p15534_0]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h0, h14801, h15451, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h0, h14801, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h15173, hlam, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h15234, hlam, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h14801, hlam, p15534_0]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [hlam, p15534_0]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h0, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p15460_1, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h15449, hlam, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h15451, hlam, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h14804, hlam, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h15446, hlam, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [hlam, p15534_0]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h15455, hlam, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h15457, hlam, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h14799, h15173, h15444, hc23, hc35, hlam, hphi, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h15444, h15449, hc23, hc35, hlam, hphi, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h15455, hc23, hc35, hlam, hphi, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [hlam, p15534_0]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h14799, h14805, h15234, h15444, h15459, hc23, hc34, hlam, hphi, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h14799, h14805, h15234, h15444, hc23, hc45, hlam, hphi, ht34, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h15444, h15447, h15451, hc23, hc45, hlam, hphi, ht34, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h15453, h15457, hc23, hc45, hlam, hphi, ht34, p15534_1]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [h15459, hlam, p15534_0]
                                                  · have p15534_0 := h15534c.1
                                                    have p15534_1 := h15534c.2.1
                                                    have p15534_2 := h15534c.2.2.1
                                                    have p15534_3 := h15534c.2.2.2
                                                    linarith only [hlam, p15534_0]
                                                · linarith only [h15533, hlam, p15491_0]
                                              · linarith only [h14805, h15532, hlam]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        rcases p15491_3 (m.d 0 3) (by simp) with h15562 | h15562
                                        · linarith only [h15173, h15562, hlam]
                                        · linarith only [h14799, h15562, hlam]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        rcases p15491_3 (m.d 0 3) (by simp) with h15565 | h15565
                                        · linarith only [h15173, h15565, hlam]
                                        · linarith only [h14802, h15565, hlam]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [h15459, hlam, p15491_0]
                                      · have p15491_0 := h15491c.1
                                        have p15491_1 := h15491c.2.1
                                        have p15491_2 := h15491c.2.2.1
                                        have p15491_3 := h15491c.2.2.2
                                        linarith only [hlam, p15491_0]
                              · linarith only [h15446, h15484, hlam]
                            · linarith only [h15483, hlam, p15460_0]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            rcases p15460_3 (m.d 0 1) (by simp) with h15572 | h15572
                            · linarith only [h15572, hlam, p15460_0]
                            · rcases p15460_3 (m.d 1 2) (by simp) with h15574 | h15574
                              · rcases p15460_3 (m.d 1 3) (by simp) with h15575 | h15575
                                · linarith only [h15444, h15575, hlam]
                                · rcases p15460_3 (m.d 1 4) (by simp) with h15577 | h15577
                                  · linarith only [h15445, h15577, hlam]
                                  · rcases p15460_3 (m.d 1 5) (by simp) with h15579 | h15579
                                    · linarith only [h15446, h15579, hlam]
                                    · rcases h3bigk with h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c | h15581c
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h14799, h15444, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15460_1, p15581_1]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h14801, h14805, h15234, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15460_1, p15581_1]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h14805, hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h15173, hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h14799, hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h14799, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15460_1, p15581_1]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h15447, hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h15449, hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h14802, hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h15444, hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h15453, hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h15455, hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        rcases p15581_3 (m.d 0 3) (by simp) with h15597 | h15597
                                        · linarith only [h15597, hlam, p15581_0]
                                        · rcases p15581_3 (m.d 1 3) (by simp) with h15599 | h15599
                                          · linarith only [h15447, h15599, hlam]
                                          · rcases p15581_3 (m.d 2 3) (by simp) with h15601 | h15601
                                            · linarith only [h15453, h15601, hlam]
                                            · rcases p15581_3 (m.d 3 4) (by simp) with h15603 | h15603
                                              · rcases p15581_3 (m.d 3 5) (by simp) with h15604 | h15604
                                                · linarith only [h15459, h15604, hlam]
                                                · linarith only [h15173, h15604, hlam]
                                              · linarith only [h15603, hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        rcases p15581_3 (m.d 0 3) (by simp) with h15608 | h15608
                                        · linarith only [h14805, h15608, hlam]
                                        · linarith only [h14799, h15608, hlam]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        rcases p15581_3 (m.d 0 3) (by simp) with h15611 | h15611
                                        · linarith only [h14805, h15611, hlam]
                                        · linarith only [h14802, h15611, hlam]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h15173, hc03, hc34, hlam, hphi, p15581_1]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        rcases p15581_3 (m.d 0 3) (by simp) with h15616 | h15616
                                        · linarith only [h15616, hlam, p15581_0]
                                        · rcases p15581_3 (m.d 1 3) (by simp) with h15618 | h15618
                                          · linarith only [h15449, h15618, hlam]
                                          · rcases p15581_3 (m.d 2 3) (by simp) with h15620 | h15620
                                            · linarith only [h15455, h15620, hlam]
                                            · rcases p15581_3 (m.d 3 4) (by simp) with h15622 | h15622
                                              · rcases p15581_3 (m.d 3 5) (by simp) with h15623 | h15623
                                                · rcases h5bigk with h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c | h15624c
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [hlam, p15624_0]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h14801, h15451, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p15460_1, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h14801, h15453, h15457, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15460_1, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h15173, hlam, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h15234, hlam, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h14801, hlam, p15624_0]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [hlam, p15624_0]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h14801, h15453, h15457, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15460_1, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h15449, hlam, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h15451, hlam, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h14804, hlam, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h15446, hlam, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [hlam, p15624_0]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h15455, hlam, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h15457, hlam, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h14804, h15453, h15457, hc23, hc35, hlam, hphi, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h15446, h15453, h15457, hc23, hc35, hlam, hphi, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h15453, h15457, hc23, hc35, hlam, hphi, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [hlam, p15624_0]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h14800, h15234, h15445, h15453, h15459, hc23, hc34, hlam, hphi, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h14800, h15234, h15445, h15453, hc23, hc45, hlam, hphi, ht34, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h15446, h15453, h15457, hc23, hc45, hlam, hphi, ht34, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h15453, h15457, hc23, hc45, hlam, hphi, ht34, p15624_1]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [h15459, hlam, p15624_0]
                                                  · have p15624_0 := h15624c.1
                                                    have p15624_1 := h15624c.2.1
                                                    have p15624_2 := h15624c.2.2.1
                                                    have p15624_3 := h15624c.2.2.2
                                                    linarith only [hlam, p15624_0]
                                                · linarith only [h15623, hlam, p15581_0]
                                              · linarith only [h14805, h15622, hlam]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        rcases p15581_3 (m.d 0 3) (by simp) with h15652 | h15652
                                        · linarith only [h15173, h15652, hlam]
                                        · linarith only [h14799, h15652, hlam]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        rcases p15581_3 (m.d 0 3) (by simp) with h15655 | h15655
                                        · linarith only [h15173, h15655, hlam]
                                        · linarith only [h14802, h15655, hlam]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [h15459, hlam, p15581_0]
                                      · have p15581_0 := h15581c.1
                                        have p15581_1 := h15581c.2.1
                                        have p15581_2 := h15581c.2.2.1
                                        have p15581_3 := h15581c.2.2.2
                                        linarith only [hlam, p15581_0]
                              · linarith only [h15574, hlam, p15460_0]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [hlam, p15460_0]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            rcases p15460_3 (m.d 0 1) (by simp) with h15662 | h15662
                            · linarith only [h0, h15662, hlam]
                            · linarith only [h14799, h15662, hlam]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            rcases p15460_3 (m.d 0 1) (by simp) with h15665 | h15665
                            · linarith only [h0, h15665, hlam]
                            · linarith only [h14800, h15665, hlam]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            rcases p15460_3 (m.d 0 1) (by simp) with h15668 | h15668
                            · linarith only [h0, h15668, hlam]
                            · linarith only [h14801, h15668, hlam]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h14799, hlam, p15460_0]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h15444, hlam, p15460_1]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [hlam, p15460_0]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h15447, hlam, p15460_1]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h15449, hlam, p15460_1]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h14800, hlam, p15460_0]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h15445, hlam, p15460_1]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h0, h14801, h15451, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15460_1]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [hlam, p15460_0]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h15451, hlam, p15460_1]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h14801, hlam, p15460_0]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h15446, hlam, p15460_1]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h0, h14801, h15444, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15460_1]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [h0, h14801, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p15460_1]
                          · have p15460_0 := h15460c.1
                            have p15460_1 := h15460c.2.1
                            have p15460_2 := h15460c.2.2.1
                            have p15460_3 := h15460c.2.2.2
                            linarith only [hlam, p15460_0]
                        · rcases h1bigk with h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c | h15686c
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [hlam, p15686_0]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h0, hlam, p15686_0]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            rcases p15686_3 (m.d 0 1) (by simp) with h15689 | h15689
                            · rcases p15686_3 (m.d 1 2) (by simp) with h15690 | h15690
                              · rcases p15686_3 (m.d 1 3) (by simp) with h15691 | h15691
                                · linarith only [h15691, hlam, p15686_0]
                                · rcases p15686_3 (m.d 1 4) (by simp) with h15693 | h15693
                                  · linarith only [h14800, h15693, hlam]
                                  · linarith only [h15447, h15693, hlam]
                              · linarith only [h15444, h15690, hlam]
                            · linarith only [h15689, hlam, p15686_0]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            rcases p15686_3 (m.d 0 1) (by simp) with h15698 | h15698
                            · rcases p15686_3 (m.d 1 2) (by simp) with h15699 | h15699
                              · rcases p15686_3 (m.d 1 3) (by simp) with h15700 | h15700
                                · linarith only [h14799, h15700, hlam]
                                · rcases p15686_3 (m.d 1 4) (by simp) with h15702 | h15702
                                  · linarith only [h15702, hlam, p15686_0]
                                  · rcases p15686_3 (m.d 1 5) (by simp) with h15704 | h15704
                                    · linarith only [h14801, h15704, hlam]
                                    · linarith only [h15451, h15704, hlam]
                              · linarith only [h15445, h15699, hlam]
                            · linarith only [h15698, hlam, p15686_0]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            rcases p15686_3 (m.d 0 1) (by simp) with h15709 | h15709
                            · rcases p15686_3 (m.d 1 2) (by simp) with h15710 | h15710
                              · rcases p15686_3 (m.d 1 3) (by simp) with h15711 | h15711
                                · linarith only [h14799, h15711, hlam]
                                · rcases p15686_3 (m.d 1 4) (by simp) with h15713 | h15713
                                  · linarith only [h14800, h15713, hlam]
                                  · rcases p15686_3 (m.d 1 5) (by simp) with h15715 | h15715
                                    · linarith only [h15715, hlam, p15686_0]
                                    · rcases h3bigk with h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c | h15717c
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h14805, h15444, h15459, hc23, hc45, hlam, hphi, ht34, p15717_1]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h14805, h15459, hc23, hc45, hlam, hphi, ht34, p15717_1]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h14805, hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h15173, hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h14799, hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h0, h14799, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15717_1]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h15447, hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h15449, hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h14802, hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h15444, hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h15453, hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h15455, hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h15459, hc03, hc45, hlam, hphi, ht34, p15717_1]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h15444, h15459, hc23, hc45, hlam, hphi, ht34, p15717_1]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h15459, hc23, hc45, hlam, hphi, ht34, p15717_1]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [hlam, p15717_0]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h15459, hlam, p15717_1]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        rcases p15717_3 (m.d 0 3) (by simp) with h15738 | h15738
                                        · linarith only [h15738, hlam, p15717_0]
                                        · rcases p15717_3 (m.d 1 3) (by simp) with h15740 | h15740
                                          · linarith only [h15449, h15740, hlam]
                                          · rcases p15717_3 (m.d 2 3) (by simp) with h15742 | h15742
                                            · linarith only [h15455, h15742, hlam]
                                            · rcases p15717_3 (m.d 3 4) (by simp) with h15744 | h15744
                                              · linarith only [h15459, h15744, hlam]
                                              · linarith only [h14805, h15744, hlam]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        rcases p15717_3 (m.d 0 3) (by simp) with h15747 | h15747
                                        · linarith only [h15173, h15747, hlam]
                                        · linarith only [h14799, h15747, hlam]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        rcases p15717_3 (m.d 0 3) (by simp) with h15750 | h15750
                                        · linarith only [h15173, h15750, hlam]
                                        · linarith only [h14802, h15750, hlam]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [h14799, h14805, h15444, h15459, hc23, hc45, hlam, hphi, ht34, p15717_1]
                                      · have p15717_0 := h15717c.1
                                        have p15717_1 := h15717c.2.1
                                        have p15717_2 := h15717c.2.2.1
                                        have p15717_3 := h15717c.2.2.2
                                        linarith only [hlam, p15717_0]
                              · linarith only [h15446, h15710, hlam]
                            · linarith only [h15709, hlam, p15686_0]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            rcases p15686_3 (m.d 0 1) (by simp) with h15757 | h15757
                            · linarith only [h15757, hlam, p15686_0]
                            · rcases p15686_3 (m.d 1 2) (by simp) with h15759 | h15759
                              · rcases p15686_3 (m.d 1 3) (by simp) with h15760 | h15760
                                · linarith only [h15444, h15760, hlam]
                                · rcases p15686_3 (m.d 1 4) (by simp) with h15762 | h15762
                                  · linarith only [h15445, h15762, hlam]
                                  · rcases p15686_3 (m.d 1 5) (by simp) with h15764 | h15764
                                    · linarith only [h15446, h15764, hlam]
                                    · rcases h3bigk with h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c | h15766c
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h14805, h15444, hc23, hc34, hlam, hphi, p15766_1]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h14799, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15686_1, p15766_1]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h14805, hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h15173, hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h14799, hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h14799, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15686_1, p15766_1]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h15447, hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h15449, hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h14802, hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h15444, hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h15453, hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h15455, hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h15459, hc03, hc45, hlam, hphi, ht34, p15766_1]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h15444, h15459, hc23, hc45, hlam, hphi, ht34, p15766_1]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h15459, hc23, hc45, hlam, hphi, ht34, p15766_1]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [hlam, p15766_0]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h15459, hlam, p15766_1]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        rcases p15766_3 (m.d 0 3) (by simp) with h15787 | h15787
                                        · linarith only [h15787, hlam, p15766_0]
                                        · rcases p15766_3 (m.d 1 3) (by simp) with h15789 | h15789
                                          · linarith only [h15449, h15789, hlam]
                                          · rcases p15766_3 (m.d 2 3) (by simp) with h15791 | h15791
                                            · linarith only [h15455, h15791, hlam]
                                            · rcases p15766_3 (m.d 3 4) (by simp) with h15793 | h15793
                                              · linarith only [h15459, h15793, hlam]
                                              · linarith only [h14805, h15793, hlam]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        rcases p15766_3 (m.d 0 3) (by simp) with h15796 | h15796
                                        · linarith only [h15173, h15796, hlam]
                                        · linarith only [h14799, h15796, hlam]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        rcases p15766_3 (m.d 0 3) (by simp) with h15799 | h15799
                                        · linarith only [h15173, h15799, hlam]
                                        · linarith only [h14802, h15799, hlam]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [h14799, h14805, h15444, h15459, hc23, hc45, hlam, hphi, ht34, p15766_1]
                                      · have p15766_0 := h15766c.1
                                        have p15766_1 := h15766c.2.1
                                        have p15766_2 := h15766c.2.2.1
                                        have p15766_3 := h15766c.2.2.2
                                        linarith only [hlam, p15766_0]
                              · linarith only [h15759, hlam, p15686_0]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [hlam, p15686_0]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            rcases p15686_3 (m.d 0 1) (by simp) with h15806 | h15806
                            · linarith only [h0, h15806, hlam]
                            · linarith only [h14799, h15806, hlam]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            rcases p15686_3 (m.d 0 1) (by simp) with h15809 | h15809
                            · linarith only [h0, h15809, hlam]
                            · linarith only [h14800, h15809, hlam]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            rcases p15686_3 (m.d 0 1) (by simp) with h15812 | h15812
                            · linarith only [h0, h15812, hlam]
                            · linarith only [h14801, h15812, hlam]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h14799, hlam, p15686_0]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h15444, hlam, p15686_1]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [hlam, p15686_0]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h15447, hlam, p15686_1]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h15449, hlam, p15686_1]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h14800, hlam, p15686_0]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h15445, hlam, p15686_1]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h0, h14801, h15451, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15686_1]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [hlam, p15686_0]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h15451, hlam, p15686_1]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h14801, hlam, p15686_0]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h15446, hlam, p15686_1]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h0, h14801, h15444, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15686_1]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [h0, h14801, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p15686_1]
                          · have p15686_0 := h15686c.1
                            have p15686_1 := h15686c.2.1
                            have p15686_2 := h15686c.2.2.1
                            have p15686_3 := h15686c.2.2.2
                            linarith only [hlam, p15686_0]
          · linarith only [h0, h14804, h15446, hlam]
        · linarith only [h0, h14803, h15445, hlam]
      · linarith only [h0, h14802, h15444, hlam]

set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14800 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14801 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14802 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14803 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14804 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h14805 | h14805
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 h14799 h14800 h14801 h14802 h14803 h14804 h14805
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 h14799 h14800 h14801 h14802 h14803 h14804 h14805

set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14800 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14801 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14802 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14803 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14804 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  linarith only [h0, h14801, h14804, hlam]

set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14800 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14801 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14802 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14803 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h14804 | h14804
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 h14799 h14800 h14801 h14802 h14803 h14804
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 h14799 h14800 h14801 h14802 h14803 h14804

set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14800 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14801 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14802 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14803 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  linarith only [h0, h14800, h14803, hlam]

set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14800 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14801 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14802 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h14803 | h14803
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 h14799 h14800 h14801 h14802 h14803
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 h14799 h14800 h14801 h14802 h14803

set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14800 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14801 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14802 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  linarith only [h0, h14799, h14802, hlam]

set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14800 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14801 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h14802 | h14802
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 h14799 h14800 h14801 h14802
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 h14799 h14800 h14801 h14802

end R2N4
