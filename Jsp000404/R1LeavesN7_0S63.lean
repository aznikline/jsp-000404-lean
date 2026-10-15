import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  rcases m.htr 0 3 5 (by decide) (by decide) with h33194 | h33194
  · rcases m.htr 0 4 5 (by decide) (by decide) with h33195 | h33195
    · rcases m.htr 1 2 3 (by decide) (by decide) with h33196 | h33196
      · rcases m.htr 1 2 4 (by decide) (by decide) with h33197 | h33197
        · rcases m.htr 1 2 5 (by decide) (by decide) with h33198 | h33198
          · rcases m.htr 1 3 4 (by decide) (by decide) with h33199 | h33199
            · rcases m.htr 1 3 5 (by decide) (by decide) with h33200 | h33200
              · rcases m.htr 1 4 5 (by decide) (by decide) with h33201 | h33201
                · rcases m.htr 2 3 4 (by decide) (by decide) with h33202 | h33202
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h33203 | h33203
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h33204 | h33204
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h33205 | h33205
                        · linarith only [h0, h33187, h33196, h33202, h33205, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h33187, h33199, h33201, h33205, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h33187, h33199, h33201, h33204, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h33187, h33200, h33203, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h33187, h33199, h33202, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h33211 | h33211
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h33212 | h33212
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h33213 | h33213
                      · linarith only [h33197, h33201, h33213, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h33215 | h33215
                        · linarith only [h33197, h33201, h33211, h33215, hlam]
                        · rcases h1bigk with h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c | h33217c
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h0, hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h0, h33196, h33212, h33215, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p33217_1]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            rcases p33217_3 (m.d 0 1) (by simp) with h33221 | h33221
                            · rcases p33217_3 (m.d 1 2) (by simp) with h33222 | h33222
                              · rcases p33217_3 (m.d 1 3) (by simp) with h33223 | h33223
                                · linarith only [h33187, h33223, hlam]
                                · linarith only [h33199, h33223, hlam]
                              · linarith only [h33197, h33222, hlam]
                            · linarith only [h33221, hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            rcases p33217_3 (m.d 0 1) (by simp) with h33228 | h33228
                            · rcases p33217_3 (m.d 1 2) (by simp) with h33229 | h33229
                              · rcases p33217_3 (m.d 1 3) (by simp) with h33230 | h33230
                                · linarith only [h33187, h33230, hlam]
                                · linarith only [h33200, h33230, hlam]
                              · linarith only [h33198, h33229, hlam]
                            · linarith only [h33228, hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h33187, h33193, h33195, h33201, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p33217_1]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            rcases p33217_3 (m.d 0 1) (by simp) with h33237 | h33237
                            · linarith only [h0, h33237, hlam]
                            · linarith only [h33187, h33237, hlam]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h0, h33187, h33193, h33195, h33201, hlam, p33217_2]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            rcases p33217_3 (m.d 0 1) (by simp) with h33241 | h33241
                            · linarith only [h0, h33241, hlam]
                            · linarith only [h33189, h33241, hlam]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h33187, hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h33196, hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h0, h33187, h33197, h33211, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p33217_1]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h0, h33187, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p33217_1]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h33188, hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h33197, hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h33199, hlam, p33217_1]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h33201, hlam, p33217_1]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h33189, hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h33198, hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h33200, hlam, p33217_0]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [h0, h33189, h33197, h33211, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p33217_1]
                          · have p33217_0 := h33217c.1
                            have p33217_1 := h33217c.2.1
                            have p33217_2 := h33217c.2.2.1
                            have p33217_3 := h33217c.2.2.2
                            linarith only [hlam, p33217_0]
                    · linarith only [h0, h33187, h33200, h33212, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h33187, h33199, h33211, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h33187, h33194, h33199, h33200, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h33262 | h33262
              · linarith only [h0, h33187, h33193, h33199, h33262, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h33264 | h33264
                · rcases m.htr 2 3 4 (by decide) (by decide) with h33265 | h33265
                  · linarith only [h33196, h33199, h33265, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h33267 | h33267
                    · linarith only [h33196, h33262, h33267, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h33269 | h33269
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h33270 | h33270
                        · rcases h1bigk with h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c | h33271c
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h0, hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            rcases p33271_3 (m.d 0 1) (by simp) with h33274 | h33274
                            · rcases p33271_3 (m.d 1 2) (by simp) with h33275 | h33275
                              · rcases p33271_3 (m.d 1 3) (by simp) with h33276 | h33276
                                · linarith only [h33276, hlam, p33271_0]
                                · rcases p33271_3 (m.d 1 4) (by simp) with h33278 | h33278
                                  · linarith only [h33188, h33278, hlam]
                                  · linarith only [h33199, h33278, hlam]
                              · linarith only [h33196, h33275, hlam]
                            · linarith only [h33274, hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h0, h33197, h33269, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p33271_1]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            rcases p33271_3 (m.d 0 1) (by simp) with h33284 | h33284
                            · rcases p33271_3 (m.d 1 2) (by simp) with h33285 | h33285
                              · rcases p33271_3 (m.d 1 3) (by simp) with h33286 | h33286
                                · linarith only [h33187, h33286, hlam]
                                · rcases p33271_3 (m.d 1 4) (by simp) with h33288 | h33288
                                  · linarith only [h33188, h33288, hlam]
                                  · linarith only [h33264, h33288, hlam]
                              · linarith only [h33198, h33285, hlam]
                            · linarith only [h33284, hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h33187, h33193, h33262, h33270, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33271_1]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h0, h33187, h33193, h33262, h33270, hlam, p33271_2]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            rcases p33271_3 (m.d 0 1) (by simp) with h33296 | h33296
                            · linarith only [h0, h33296, hlam]
                            · linarith only [h33188, h33296, hlam]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            rcases p33271_3 (m.d 0 1) (by simp) with h33299 | h33299
                            · linarith only [h0, h33299, hlam]
                            · linarith only [h33189, h33299, hlam]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h33187, hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h33196, hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h33199, hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h33262, hlam, p33271_1]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h33188, hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h33197, hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h0, h33188, h33196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33271_1]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h0, h33187, h33193, h33199, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p33271_1]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h33189, hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h33198, hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h0, h33189, h33196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33271_1]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [h33264, hlam, p33271_0]
                          · have p33271_0 := h33271c.1
                            have p33271_1 := h33271c.2.1
                            have p33271_2 := h33271c.2.2.1
                            have p33271_3 := h33271c.2.2.2
                            linarith only [hlam, p33271_0]
                        · linarith only [h33197, h33199, h33269, h33270, hlam]
                      · linarith only [h0, h33188, h33264, h33269, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h33319 | h33319
                  · linarith only [h33196, h33199, h33319, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h33321 | h33321
                    · linarith only [h0, h33187, h33193, h33195, h33196, h33199, h33264, h33321, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h33323 | h33323
                      · linarith only [h33197, h33264, h33323, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h33325 | h33325
                        · linarith only [h0, h33187, h33193, h33264, h33325, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h33187, h33193, h33195, h33196, h33199, h33325, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h33192, h33198, hlam]
        · linarith only [h0, h33191, h33197, hlam]
      · linarith only [h0, h33190, h33196, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h33331 | h33331
      · rcases m.htr 1 2 4 (by decide) (by decide) with h33332 | h33332
        · rcases m.htr 1 2 5 (by decide) (by decide) with h33333 | h33333
          · rcases m.htr 1 3 4 (by decide) (by decide) with h33334 | h33334
            · rcases m.htr 1 3 5 (by decide) (by decide) with h33335 | h33335
              · rcases m.htr 1 4 5 (by decide) (by decide) with h33336 | h33336
                · linarith only [h0, h33188, h33195, h33336, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h33338 | h33338
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h33339 | h33339
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h33340 | h33340
                      · linarith only [h33188, h33195, h33332, h33340, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h33342 | h33342
                        · linarith only [h0, h33187, h33193, h33195, h33342, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h1bigk with h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c | h33344c
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h0, hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h0, h33331, h33339, h33342, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p33344_1]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            rcases p33344_3 (m.d 0 1) (by simp) with h33348 | h33348
                            · rcases p33344_3 (m.d 1 2) (by simp) with h33349 | h33349
                              · rcases p33344_3 (m.d 1 3) (by simp) with h33350 | h33350
                                · linarith only [h33187, h33350, hlam]
                                · linarith only [h33334, h33350, hlam]
                              · linarith only [h33332, h33349, hlam]
                            · linarith only [h33348, hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            rcases p33344_3 (m.d 0 1) (by simp) with h33355 | h33355
                            · rcases p33344_3 (m.d 1 2) (by simp) with h33356 | h33356
                              · rcases p33344_3 (m.d 1 3) (by simp) with h33357 | h33357
                                · linarith only [h33187, h33357, hlam]
                                · linarith only [h33335, h33357, hlam]
                              · linarith only [h33333, h33356, hlam]
                            · linarith only [h33355, hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h33187, h33331, h33339, h33342, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p33344_1]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            rcases p33344_3 (m.d 0 1) (by simp) with h33364 | h33364
                            · linarith only [h0, h33364, hlam]
                            · linarith only [h33187, h33364, hlam]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            rcases p33344_3 (m.d 0 1) (by simp) with h33367 | h33367
                            · linarith only [h0, h33367, hlam]
                            · linarith only [h33188, h33367, hlam]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            rcases p33344_3 (m.d 0 1) (by simp) with h33370 | h33370
                            · linarith only [h0, h33370, hlam]
                            · linarith only [h33189, h33370, hlam]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h33187, hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h33331, hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h0, h33187, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p33344_1]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h0, h33187, h33332, h33336, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p33344_1]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h33188, hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h33332, hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h33334, hlam, p33344_1]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h33336, hlam, p33344_1]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h33189, hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h33333, hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h33335, hlam, p33344_0]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [h0, h33189, h33332, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p33344_1]
                          · have p33344_0 := h33344c.1
                            have p33344_1 := h33344c.2.1
                            have p33344_2 := h33344c.2.2.1
                            have p33344_3 := h33344c.2.2.2
                            linarith only [hlam, p33344_0]
                    · linarith only [h0, h33187, h33335, h33339, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h33187, h33334, h33338, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h33187, h33194, h33334, h33335, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h33391 | h33391
              · linarith only [h0, h33187, h33193, h33334, h33391, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h33393 | h33393
                · linarith only [h0, h33188, h33195, h33393, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h33395 | h33395
                  · linarith only [h33331, h33334, h33395, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h33397 | h33397
                    · linarith only [h0, h33187, h33193, h33331, h33334, h33391, h33397, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h33399 | h33399
                      · linarith only [h33191, h33193, h33195, h33331, h33334, h33399, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h33401 | h33401
                        · linarith only [h33193, h33195, h33401, hlam]
                        · rcases h1bigk with h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c | h33403c
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h0, hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            rcases p33403_3 (m.d 0 1) (by simp) with h33406 | h33406
                            · rcases p33403_3 (m.d 1 2) (by simp) with h33407 | h33407
                              · rcases p33403_3 (m.d 1 3) (by simp) with h33408 | h33408
                                · linarith only [h33408, hlam, p33403_0]
                                · rcases p33403_3 (m.d 1 4) (by simp) with h33410 | h33410
                                  · linarith only [h33188, h33410, hlam]
                                  · linarith only [h33334, h33410, hlam]
                              · linarith only [h33331, h33407, hlam]
                            · linarith only [h33406, hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            rcases p33403_3 (m.d 0 1) (by simp) with h33415 | h33415
                            · rcases p33403_3 (m.d 1 2) (by simp) with h33416 | h33416
                              · rcases p33403_3 (m.d 1 3) (by simp) with h33417 | h33417
                                · linarith only [h33187, h33417, hlam]
                                · rcases p33403_3 (m.d 1 4) (by simp) with h33419 | h33419
                                  · linarith only [h33419, hlam, p33403_0]
                                  · rcases p33403_3 (m.d 1 5) (by simp) with h33421 | h33421
                                    · linarith only [h33189, h33421, hlam]
                                    · linarith only [h33393, h33421, hlam]
                              · linarith only [h33332, h33416, hlam]
                            · linarith only [h33415, hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            rcases p33403_3 (m.d 0 1) (by simp) with h33426 | h33426
                            · rcases p33403_3 (m.d 1 2) (by simp) with h33427 | h33427
                              · rcases p33403_3 (m.d 1 3) (by simp) with h33428 | h33428
                                · linarith only [h33187, h33428, hlam]
                                · rcases p33403_3 (m.d 1 4) (by simp) with h33430 | h33430
                                  · linarith only [h33188, h33430, hlam]
                                  · rcases p33403_3 (m.d 1 5) (by simp) with h33432 | h33432
                                    · linarith only [h33432, hlam, p33403_0]
                                    · rcases h1emax with h33434 | h33434 | h33434 | h33434 | h33434
                                      · linarith only [h33187, h33194, h33331, h33334, h33401, h33434, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                      · linarith only [h0, h33187, h33194, h33331, h33334, h33401, h33434, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                      · rcases h2bigk with h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c | h33437c
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h0, hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          rcases p33437_3 (m.d 0 2) (by simp) with h33440 | h33440
                                          · rcases p33437_3 (m.d 1 2) (by simp) with h33441 | h33441
                                            · rcases p33437_3 (m.d 2 3) (by simp) with h33442 | h33442
                                              · linarith only [h33442, hlam, p33437_0]
                                              · rcases p33437_3 (m.d 2 4) (by simp) with h33444 | h33444
                                                · linarith only [h33191, h33444, hlam]
                                                · linarith only [h33395, h33444, hlam]
                                            · linarith only [h33331, h33441, hlam]
                                          · linarith only [h33440, hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          rcases p33437_3 (m.d 0 2) (by simp) with h33449 | h33449
                                          · rcases p33437_3 (m.d 1 2) (by simp) with h33450 | h33450
                                            · rcases p33437_3 (m.d 2 3) (by simp) with h33451 | h33451
                                              · linarith only [h33190, h33451, hlam]
                                              · rcases p33437_3 (m.d 2 4) (by simp) with h33453 | h33453
                                                · linarith only [h33453, hlam, p33437_0]
                                                · rcases p33437_3 (m.d 2 5) (by simp) with h33455 | h33455
                                                  · linarith only [h33192, h33455, hlam]
                                                  · linarith only [h33399, h33455, hlam]
                                            · linarith only [h33332, h33450, hlam]
                                          · linarith only [h33449, hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          rcases p33437_3 (m.d 0 2) (by simp) with h33460 | h33460
                                          · rcases p33437_3 (m.d 1 2) (by simp) with h33461 | h33461
                                            · rcases p33437_3 (m.d 2 3) (by simp) with h33462 | h33462
                                              · linarith only [h33190, h33462, hlam]
                                              · rcases p33437_3 (m.d 2 4) (by simp) with h33464 | h33464
                                                · linarith only [h33191, h33464, hlam]
                                                · rcases p33437_3 (m.d 2 5) (by simp) with h33466 | h33466
                                                  · linarith only [h33466, hlam, p33437_0]
                                                  · rcases h4bigk with h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c | h33468c
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [hlam, p33468_0]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33195, h33331, h33334, hc23, hc45, hlam, hphi, ht34, p33468_1]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33195, h33395, hc23, hc45, hlam, hphi, ht34, p33468_1]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33195, h33331, h33334, hc23, hc45, hlam, hphi, ht34, p33468_1]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33195, hlam, p33468_0]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33188, hlam, p33468_0]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [hlam, p33468_0]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h0, h33188, h33395, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33468_1]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33334, hlam, p33468_1]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33393, hlam, p33468_0]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33191, hlam, p33468_0]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33332, hlam, p33468_0]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [hlam, p33468_0]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33395, hlam, p33468_1]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33399, hlam, p33468_0]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33193, hlam, p33468_0]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h0, h33187, h33194, h33401, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p33468_1]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h0, h33187, h33194, h33395, h33401, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33468_1]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [hlam, p33468_0]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33401, hlam, p33468_0]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33193, h33331, h33334, hc23, hc45, hlam, hphi, ht34, p33468_1]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      rcases p33468_3 (m.d 0 4) (by simp) with h33490 | h33490
                                                      · linarith only [h33195, h33490, hlam]
                                                      · linarith only [h33188, h33490, hlam]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      rcases p33468_3 (m.d 0 4) (by simp) with h33493 | h33493
                                                      · linarith only [h33195, h33493, hlam]
                                                      · linarith only [h33191, h33493, hlam]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [h33331, h33334, hc23, hc45, hlam, hphi, ht34, p33468_1]
                                                    · have p33468_0 := h33468c.1
                                                      have p33468_1 := h33468c.2.1
                                                      have p33468_2 := h33468c.2.2.1
                                                      have p33468_3 := h33468c.2.2.2
                                                      linarith only [hlam, p33468_0]
                                            · linarith only [h33333, h33461, hlam]
                                          · linarith only [h33460, hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p33403_1, p33437_1]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h0, h33187, h33193, h33331, h33334, hlam, p33437_2]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h0, h33333, h33399, hlam, p33403_1, p33437_2]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h0, h33333, hlam, p33403_1, p33437_2]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h33190, hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h33331, hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h33395, hlam, p33437_1]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h33397, hlam, p33437_1]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h33191, hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h33332, hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h33333, h33399, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p33403_1, p33437_1]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h33399, hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h33192, hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h33333, hlam, p33437_0]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h0, h33333, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33403_1, p33437_1]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [h0, h33333, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p33403_1, p33437_1]
                                        · have p33437_0 := h33437c.1
                                          have p33437_1 := h33437c.2.1
                                          have p33437_2 := h33437c.2.2.1
                                          have p33437_3 := h33437c.2.2.2
                                          linarith only [hlam, p33437_0]
                                      · rcases h2bigk with h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c | h33520c
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h0, hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          rcases p33520_3 (m.d 0 2) (by simp) with h33523 | h33523
                                          · rcases p33520_3 (m.d 1 2) (by simp) with h33524 | h33524
                                            · rcases p33520_3 (m.d 2 3) (by simp) with h33525 | h33525
                                              · linarith only [h33525, hlam, p33520_0]
                                              · rcases p33520_3 (m.d 2 4) (by simp) with h33527 | h33527
                                                · linarith only [h33191, h33527, hlam]
                                                · linarith only [h33395, h33527, hlam]
                                            · linarith only [h33331, h33524, hlam]
                                          · linarith only [h33523, hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          rcases p33520_3 (m.d 0 2) (by simp) with h33532 | h33532
                                          · rcases p33520_3 (m.d 1 2) (by simp) with h33533 | h33533
                                            · rcases p33520_3 (m.d 2 3) (by simp) with h33534 | h33534
                                              · linarith only [h33190, h33534, hlam]
                                              · rcases p33520_3 (m.d 2 4) (by simp) with h33536 | h33536
                                                · linarith only [h33536, hlam, p33520_0]
                                                · rcases p33520_3 (m.d 2 5) (by simp) with h33538 | h33538
                                                  · linarith only [h33192, h33538, hlam]
                                                  · linarith only [h33399, h33538, hlam]
                                            · linarith only [h33332, h33533, hlam]
                                          · linarith only [h33532, hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          rcases p33520_3 (m.d 0 2) (by simp) with h33543 | h33543
                                          · rcases p33520_3 (m.d 1 2) (by simp) with h33544 | h33544
                                            · rcases p33520_3 (m.d 2 3) (by simp) with h33545 | h33545
                                              · linarith only [h33190, h33545, hlam]
                                              · rcases p33520_3 (m.d 2 4) (by simp) with h33547 | h33547
                                                · linarith only [h33191, h33547, hlam]
                                                · rcases p33520_3 (m.d 2 5) (by simp) with h33549 | h33549
                                                  · linarith only [h33549, hlam, p33520_0]
                                                  · rcases h4bigk with h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c | h33551c
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [hlam, p33551_0]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33195, h33331, h33334, hc23, hc45, hlam, hphi, ht34, p33551_1]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33195, h33395, hc23, hc45, hlam, hphi, ht34, p33551_1]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33195, h33331, h33334, hc23, hc45, hlam, hphi, ht34, p33551_1]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33195, hlam, p33551_0]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33188, hlam, p33551_0]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [hlam, p33551_0]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h0, h33188, h33395, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33551_1]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33334, hlam, p33551_1]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33393, hlam, p33551_0]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33191, hlam, p33551_0]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33332, hlam, p33551_0]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [hlam, p33551_0]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33395, hlam, p33551_1]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33399, hlam, p33551_0]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33193, hlam, p33551_0]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h0, h33187, h33194, h33401, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p33551_1]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h0, h33187, h33194, h33395, h33401, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33551_1]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [hlam, p33551_0]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33401, hlam, p33551_0]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33193, h33331, h33334, hc23, hc45, hlam, hphi, ht34, p33551_1]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      rcases p33551_3 (m.d 0 4) (by simp) with h33573 | h33573
                                                      · linarith only [h33195, h33573, hlam]
                                                      · linarith only [h33188, h33573, hlam]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      rcases p33551_3 (m.d 0 4) (by simp) with h33576 | h33576
                                                      · linarith only [h33195, h33576, hlam]
                                                      · linarith only [h33191, h33576, hlam]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [h33331, h33334, hc23, hc45, hlam, hphi, ht34, p33551_1]
                                                    · have p33551_0 := h33551c.1
                                                      have p33551_1 := h33551c.2.1
                                                      have p33551_2 := h33551c.2.2.1
                                                      have p33551_3 := h33551c.2.2.2
                                                      linarith only [hlam, p33551_0]
                                            · linarith only [h33333, h33544, hlam]
                                          · linarith only [h33543, hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p33403_1, p33520_1]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h0, h33187, h33193, h33331, h33334, hlam, p33520_2]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h0, h33332, h33393, hlam, p33403_1, p33520_2]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h0, h33333, hlam, p33403_1, p33520_2]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h33190, hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h33331, hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h33395, hlam, p33520_1]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h33397, hlam, p33520_1]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h33191, hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h33332, hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h33332, h33393, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p33403_1, p33520_1]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h33399, hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h33192, hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h33333, hlam, p33520_0]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h0, h33333, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33403_1, p33520_1]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [h0, h33333, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p33403_1, p33520_1]
                                        · have p33520_0 := h33520c.1
                                          have p33520_1 := h33520c.2.1
                                          have p33520_2 := h33520c.2.2.1
                                          have p33520_3 := h33520c.2.2.2
                                          linarith only [hlam, p33520_0]
                                      · rcases h2bigk with h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c | h33603c
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h0, hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          rcases p33603_3 (m.d 0 2) (by simp) with h33606 | h33606
                                          · rcases p33603_3 (m.d 1 2) (by simp) with h33607 | h33607
                                            · rcases p33603_3 (m.d 2 3) (by simp) with h33608 | h33608
                                              · linarith only [h33608, hlam, p33603_0]
                                              · rcases p33603_3 (m.d 2 4) (by simp) with h33610 | h33610
                                                · linarith only [h33191, h33610, hlam]
                                                · linarith only [h33395, h33610, hlam]
                                            · linarith only [h33331, h33607, hlam]
                                          · linarith only [h33606, hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          rcases p33603_3 (m.d 0 2) (by simp) with h33615 | h33615
                                          · rcases p33603_3 (m.d 1 2) (by simp) with h33616 | h33616
                                            · rcases p33603_3 (m.d 2 3) (by simp) with h33617 | h33617
                                              · linarith only [h33190, h33617, hlam]
                                              · rcases p33603_3 (m.d 2 4) (by simp) with h33619 | h33619
                                                · linarith only [h33619, hlam, p33603_0]
                                                · rcases p33603_3 (m.d 2 5) (by simp) with h33621 | h33621
                                                  · linarith only [h33192, h33621, hlam]
                                                  · linarith only [h33399, h33621, hlam]
                                            · linarith only [h33332, h33616, hlam]
                                          · linarith only [h33615, hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          rcases p33603_3 (m.d 0 2) (by simp) with h33626 | h33626
                                          · rcases p33603_3 (m.d 1 2) (by simp) with h33627 | h33627
                                            · rcases p33603_3 (m.d 2 3) (by simp) with h33628 | h33628
                                              · linarith only [h33190, h33628, hlam]
                                              · rcases p33603_3 (m.d 2 4) (by simp) with h33630 | h33630
                                                · linarith only [h33191, h33630, hlam]
                                                · rcases p33603_3 (m.d 2 5) (by simp) with h33632 | h33632
                                                  · linarith only [h33632, hlam, p33603_0]
                                                  · rcases h4bigk with h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c | h33634c
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [hlam, p33634_0]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33195, hc14, hc45, hlam, hphi, p33634_1]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33195, h33395, hc23, hc45, hlam, hphi, ht34, p33634_1]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h0, h33187, h33194, h33195, h33331, h33334, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33634_1]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33195, hlam, p33634_0]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33188, hlam, p33634_0]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [hlam, p33634_0]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h0, h33188, h33395, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33634_1]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33334, hlam, p33634_1]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33393, hlam, p33634_0]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33191, hlam, p33634_0]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33332, hlam, p33634_0]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [hlam, p33634_0]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33395, hlam, p33634_1]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33399, hlam, p33634_0]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33193, hlam, p33634_0]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h0, h33187, h33193, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p33634_1]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h0, h33187, h33194, h33395, h33401, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33634_1]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [hlam, p33634_0]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33401, hlam, p33634_0]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33193, h33331, h33334, hc23, hc45, hlam, hphi, ht34, p33634_1]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      rcases p33634_3 (m.d 0 4) (by simp) with h33656 | h33656
                                                      · linarith only [h33195, h33656, hlam]
                                                      · linarith only [h33188, h33656, hlam]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      rcases p33634_3 (m.d 0 4) (by simp) with h33659 | h33659
                                                      · linarith only [h33195, h33659, hlam]
                                                      · linarith only [h33191, h33659, hlam]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [h33331, h33334, hc23, hc45, hlam, hphi, ht34, p33634_1]
                                                    · have p33634_0 := h33634c.1
                                                      have p33634_1 := h33634c.2.1
                                                      have p33634_2 := h33634c.2.2.1
                                                      have p33634_3 := h33634c.2.2.2
                                                      linarith only [hlam, p33634_0]
                                            · linarith only [h33333, h33627, hlam]
                                          · linarith only [h33626, hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p33403_1, p33603_1]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h0, h33187, h33193, h33331, h33334, hlam, p33603_2]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h0, h33332, h33393, hlam, p33403_1, p33603_2]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h0, h33333, hlam, p33403_1, p33603_2]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h33190, hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h33331, hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h33395, hlam, p33603_1]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h33397, hlam, p33603_1]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h33191, hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h33332, hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h33332, h33393, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p33403_1, p33603_1]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h33399, hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h33192, hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h33333, hlam, p33603_0]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h0, h33333, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33403_1, p33603_1]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [h0, h33333, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p33403_1, p33603_1]
                                        · have p33603_0 := h33603c.1
                                          have p33603_1 := h33603c.2.1
                                          have p33603_2 := h33603c.2.2.1
                                          have p33603_3 := h33603c.2.2.2
                                          linarith only [hlam, p33603_0]
                              · linarith only [h33333, h33427, hlam]
                            · linarith only [h33426, hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h33187, h33193, h33331, h33334, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33403_1]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h0, h33187, h33193, h33334, hlam, p33403_2]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            rcases p33403_3 (m.d 0 1) (by simp) with h33691 | h33691
                            · linarith only [h0, h33691, hlam]
                            · linarith only [h33188, h33691, hlam]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            rcases p33403_3 (m.d 0 1) (by simp) with h33694 | h33694
                            · linarith only [h0, h33694, hlam]
                            · linarith only [h33189, h33694, hlam]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h33187, hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h33331, hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h33334, hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h33391, hlam, p33403_1]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h33188, hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h33332, hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h0, h33188, h33331, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33403_1]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h33393, hlam, p33403_1]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h33189, hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h33333, hlam, p33403_0]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h0, h33187, h33194, h33331, h33391, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33403_1]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [h0, h33187, h33194, h33391, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p33403_1]
                          · have p33403_0 := h33403c.1
                            have p33403_1 := h33403c.2.1
                            have p33403_2 := h33403c.2.2.1
                            have p33403_3 := h33403c.2.2.2
                            linarith only [hlam, p33403_0]
          · linarith only [h0, h33192, h33333, hlam]
        · linarith only [h0, h33191, h33332, hlam]
      · linarith only [h0, h33187, h33190, h33193, h33331, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h33715 | h33715
    · linarith only [h33193, h33194, h33715, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h33717 | h33717
      · rcases m.htr 1 2 4 (by decide) (by decide) with h33718 | h33718
        · rcases m.htr 1 2 5 (by decide) (by decide) with h33719 | h33719
          · rcases m.htr 1 3 4 (by decide) (by decide) with h33720 | h33720
            · rcases m.htr 1 3 5 (by decide) (by decide) with h33721 | h33721
              · linarith only [h33187, h33194, h33721, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h33723 | h33723
                · linarith only [h33188, h33715, h33723, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h33725 | h33725
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h33726 | h33726
                    · linarith only [h33187, h33194, h33717, h33726, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h33728 | h33728
                      · linarith only [h33191, h33715, h33728, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h33730 | h33730
                        · linarith only [h33189, h33715, h33717, h33721, h33725, h33730, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c | h33732c
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [hlam, p33732_0]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h0, hlam, p33732_0]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h0, h33720, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p33732_1]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            rcases p33732_3 (m.d 0 1) (by simp) with h33736 | h33736
                            · rcases p33732_3 (m.d 1 2) (by simp) with h33737 | h33737
                              · rcases p33732_3 (m.d 1 3) (by simp) with h33738 | h33738
                                · linarith only [h33187, h33738, hlam]
                                · linarith only [h33720, h33738, hlam]
                              · linarith only [h33718, h33737, hlam]
                            · linarith only [h33736, hlam, p33732_0]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h0, h33719, h33725, h33726, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p33732_1]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h33187, h33717, h33725, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p33732_1]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [hlam, p33732_0]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            rcases p33732_3 (m.d 0 1) (by simp) with h33746 | h33746
                            · linarith only [h0, h33746, hlam]
                            · linarith only [h33187, h33746, hlam]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            rcases p33732_3 (m.d 0 1) (by simp) with h33749 | h33749
                            · linarith only [h0, h33749, hlam]
                            · linarith only [h33188, h33749, hlam]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            rcases p33732_3 (m.d 0 1) (by simp) with h33752 | h33752
                            · linarith only [h0, h33752, hlam]
                            · linarith only [h33189, h33752, hlam]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h33187, hlam, p33732_0]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h33717, hlam, p33732_0]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [hlam, p33732_0]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h33187, h33194, h33730, hc14, hc45, hlam, hphi, p33732_1]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h33721, hlam, p33732_1]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h33188, hlam, p33732_0]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h33718, hlam, p33732_0]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h33720, hlam, p33732_1]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [hlam, p33732_0]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h33723, hlam, p33732_1]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h33189, hlam, p33732_0]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h33719, hlam, p33732_0]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h0, h33189, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33732_1]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [h0, h33189, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p33732_1]
                          · have p33732_0 := h33732c.1
                            have p33732_1 := h33732c.2.1
                            have p33732_2 := h33732c.2.2.1
                            have p33732_3 := h33732c.2.2.2
                            linarith only [hlam, p33732_0]
                  · linarith only [h33193, h33194, h33725, hc23, hc35, hlam, hphi]
            · linarith only [h33193, h33194, h33720, hc13, hc35, hlam, hphi]
          · linarith only [h0, h33192, h33719, hlam]
        · linarith only [h0, h33191, h33718, hlam]
      · linarith only [h0, h33190, h33717, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  rcases m.htr 0 4 5 (by decide) (by decide) with h33776 | h33776
  · rcases m.htr 1 2 3 (by decide) (by decide) with h33777 | h33777
    · rcases m.htr 1 2 4 (by decide) (by decide) with h33778 | h33778
      · rcases m.htr 1 2 5 (by decide) (by decide) with h33779 | h33779
        · rcases m.htr 1 3 4 (by decide) (by decide) with h33780 | h33780
          · linarith only [h0, h33187, h33193, h33780, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h33782 | h33782
            · rcases m.htr 1 4 5 (by decide) (by decide) with h33783 | h33783
              · rcases m.htr 2 3 4 (by decide) (by decide) with h33784 | h33784
                · linarith only [h33187, h33193, h33777, h33784, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h33786 | h33786
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h33787 | h33787
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h33788 | h33788
                      · rcases h1bigk with h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c | h33789c
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h0, hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h0, h33777, h33786, h33788, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p33789_1]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h0, h33777, h33780, h33786, h33788, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p33789_1]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          rcases p33789_3 (m.d 0 1) (by simp) with h33794 | h33794
                          · rcases p33789_3 (m.d 1 2) (by simp) with h33795 | h33795
                            · rcases p33789_3 (m.d 1 3) (by simp) with h33796 | h33796
                              · linarith only [h33187, h33796, hlam]
                              · linarith only [h33782, h33796, hlam]
                            · linarith only [h33779, h33795, hlam]
                          · linarith only [h33794, hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h33187, h33777, h33786, h33788, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p33789_1]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          rcases p33789_3 (m.d 0 1) (by simp) with h33803 | h33803
                          · linarith only [h0, h33803, hlam]
                          · linarith only [h33187, h33803, hlam]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          rcases p33789_3 (m.d 0 1) (by simp) with h33806 | h33806
                          · linarith only [h0, h33806, hlam]
                          · linarith only [h33188, h33806, hlam]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          rcases p33789_3 (m.d 0 1) (by simp) with h33809 | h33809
                          · linarith only [h0, h33809, hlam]
                          · linarith only [h33189, h33809, hlam]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h33187, hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h33777, hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h33780, hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h0, h33188, h33780, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p33789_1]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h33188, hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h33778, hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h0, h33188, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p33789_1]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h0, h33188, h33779, h33786, h33788, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p33789_1]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h33189, hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h33779, hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h33782, hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [h33783, hlam, p33789_0]
                        · have p33789_0 := h33789c.1
                          have p33789_1 := h33789c.2.1
                          have p33789_2 := h33789c.2.2.1
                          have p33789_3 := h33789c.2.2.2
                          linarith only [hlam, p33789_0]
                      · linarith only [h33187, h33193, h33776, h33777, h33786, h33788, hc04, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h33188, h33783, h33787, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h33193, h33775, h33786, hc23, hc34, hlam, hphi]
              · linarith only [h0, h33188, h33776, h33780, h33782, h33783, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h33193, h33775, h33782, hc13, hc34, hlam, hphi]
        · linarith only [h0, h33192, h33779, hlam]
      · linarith only [h0, h33191, h33778, hlam]
    · linarith only [h0, h33190, h33777, hlam]
  · linarith only [h33193, h33775, h33776, hlam]

end R2N4
