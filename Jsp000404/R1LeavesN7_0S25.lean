import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0_x1_x1_x0 (m : N7Model)
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
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14161 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14162 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14163 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h14165 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h14167 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 2 3 4 (by decide) (by decide) with h14168 | h14168
  · linarith only [h1, h14160, h14168, h7, hlam]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h14170 | h14170
    · linarith only [h1, h13284, h14160, h14170, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h14172 | h14172
      · rcases m.htr 3 4 5 (by decide) (by decide) with h14173 | h14173
        · rcases h1bigk with h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c | h14174c
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [h14161, h14172, hc01, hc45, hlam, hphi, ht0b, ht5b, p14174_1]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            rcases p14174_3 (m.d 0 1) (by simp) with h14177 | h14177
            · rcases p14174_3 (m.d 1 2) (by simp) with h14178 | h14178
              · linarith only [h0, h14178, hlam]
              · linarith only [h14160, h14178, hlam]
            · linarith only [h14177, hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            rcases p14174_3 (m.d 0 1) (by simp) with h14182 | h14182
            · rcases p14174_3 (m.d 1 2) (by simp) with h14183 | h14183
              · linarith only [h0, h14183, hlam]
              · linarith only [h14161, h14183, hlam]
            · linarith only [h14182, hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            rcases p14174_3 (m.d 0 1) (by simp) with h14187 | h14187
            · rcases p14174_3 (m.d 1 2) (by simp) with h14188 | h14188
              · linarith only [h0, h14188, hlam]
              · linarith only [h14162, h14188, hlam]
            · linarith only [h14187, hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [h0, hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            rcases p14174_3 (m.d 0 1) (by simp) with h14194 | h14194
            · rcases p14174_3 (m.d 1 2) (by simp) with h14195 | h14195
              · rcases p14174_3 (m.d 1 3) (by simp) with h14196 | h14196
                · linarith only [h14160, h14196, hlam]
                · rcases p14174_3 (m.d 1 4) (by simp) with h14198 | h14198
                  · linarith only [h14161, h14198, hlam]
                  · linarith only [h14163, h14198, hlam]
              · linarith only [h14160, h14195, hlam]
            · linarith only [h1, h14194, hlam]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [h0, h14161, h14172, hc01, hc45, hlam, hphi, ht0b, ht5b, p14174_1]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            rcases p14174_3 (m.d 0 1) (by simp) with h14204 | h14204
            · rcases p14174_3 (m.d 1 2) (by simp) with h14205 | h14205
              · rcases p14174_3 (m.d 1 3) (by simp) with h14206 | h14206
                · linarith only [h14160, h14206, hlam]
                · rcases p14174_3 (m.d 1 4) (by simp) with h14208 | h14208
                  · linarith only [h14161, h14208, hlam]
                  · linarith only [h14167, h14208, hlam]
              · linarith only [h14162, h14205, hlam]
            · linarith only [h14204, h3, hlam]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [h1, hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [h14160, hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [h14163, hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [h14165, hlam, p14174_1]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [h2, hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [h14161, hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            rcases p14174_3 (m.d 0 1) (by simp) with h14220 | h14220
            · rcases p14174_3 (m.d 1 2) (by simp) with h14221 | h14221
              · rcases p14174_3 (m.d 1 3) (by simp) with h14222 | h14222
                · linarith only [h14163, h14222, hlam]
                · rcases p14174_3 (m.d 1 4) (by simp) with h14224 | h14224
                  · rcases p14174_3 (m.d 1 5) (by simp) with h14225 | h14225
                    · linarith only [h14167, h14225, hlam]
                    · linarith only [h14165, h14225, hlam]
                  · linarith only [h14163, h14224, hlam]
              · linarith only [h14160, h14221, hlam]
            · linarith only [h1, h14220, hlam]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            rcases p14174_3 (m.d 0 1) (by simp) with h14232 | h14232
            · rcases p14174_3 (m.d 1 2) (by simp) with h14233 | h14233
              · rcases p14174_3 (m.d 1 3) (by simp) with h14234 | h14234
                · linarith only [h14163, h14234, hlam]
                · rcases p14174_3 (m.d 1 4) (by simp) with h14236 | h14236
                  · rcases p14174_3 (m.d 1 5) (by simp) with h14237 | h14237
                    · linarith only [h14167, h14237, hlam]
                    · rcases h1emax with h14239 | h14239 | h14239 | h14239 | h14239
                      · linarith only [h0, h14161, h14165, h14239, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14174_1]
                      · linarith only [h14160, h14161, h14165, h14239, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14174_1]
                      · rcases h2bigk with h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c | h14242c
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h14160, h14161, h14165, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14174_1, p14242_1]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          rcases p14242_3 (m.d 0 2) (by simp) with h14245 | h14245
                          · rcases p14242_3 (m.d 1 2) (by simp) with h14246 | h14246
                            · linarith only [h0, h14246, hlam]
                            · linarith only [h14160, h14246, hlam]
                          · linarith only [h14245, hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          rcases p14242_3 (m.d 0 2) (by simp) with h14250 | h14250
                          · rcases p14242_3 (m.d 1 2) (by simp) with h14251 | h14251
                            · linarith only [h0, h14251, hlam]
                            · linarith only [h14161, h14251, hlam]
                          · linarith only [h14250, hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          rcases p14242_3 (m.d 0 2) (by simp) with h14255 | h14255
                          · rcases p14242_3 (m.d 1 2) (by simp) with h14256 | h14256
                            · linarith only [h0, h14256, hlam]
                            · linarith only [h14162, h14256, hlam]
                          · linarith only [h14255, hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h0, hlam, p14242_1]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          rcases p14242_3 (m.d 0 2) (by simp) with h14262 | h14262
                          · rcases p14242_3 (m.d 1 2) (by simp) with h14263 | h14263
                            · rcases p14242_3 (m.d 2 3) (by simp) with h14264 | h14264
                              · linarith only [h14264, hlam, p14242_0]
                              · rcases p14242_3 (m.d 2 4) (by simp) with h14266 | h14266
                                · linarith only [h14161, h14266, hlam]
                                · linarith only [h14168, h14266, hlam]
                            · linarith only [h14263, hlam, p14242_0]
                          · linarith only [h14262, h4, hlam]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h0, h14172, hc01, hc45, hlam, hphi, ht0b, ht5b, p14242_1]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          rcases p14242_3 (m.d 0 2) (by simp) with h14272 | h14272
                          · rcases p14242_3 (m.d 1 2) (by simp) with h14273 | h14273
                            · rcases p14242_3 (m.d 2 3) (by simp) with h14274 | h14274
                              · linarith only [h14160, h14274, hlam]
                              · rcases p14242_3 (m.d 2 4) (by simp) with h14276 | h14276
                                · linarith only [h14161, h14276, hlam]
                                · linarith only [h14172, h14276, hlam]
                            · linarith only [h14273, hlam, p14242_0]
                          · linarith only [h14272, h6, hlam]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h4, hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h14160, hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h14168, hlam, p14242_1]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h14170, hlam, p14242_1]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h5, hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h14161, hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h0, h14161, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14242_1]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h0, h14161, hc01, hc25, hlam, hphi, ht0b, ht5b, p14242_1]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h6, hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h14162, hlam, p14242_0]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h0, h14162, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14242_1]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [h14172, hlam, p14242_1]
                        · have p14242_0 := h14242c.1
                          have p14242_1 := h14242c.2.1
                          have p14242_2 := h14242c.2.2.1
                          have p14242_3 := h14242c.2.2.2
                          linarith only [hlam, p14242_0]
                      · linarith only [h14160, h14165, h14239, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14174_1]
                      · rcases h2bigk with h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c | h14297c
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h0, h14160, h14161, h14165, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14174_1, p14297_1]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          rcases p14297_3 (m.d 0 2) (by simp) with h14300 | h14300
                          · rcases p14297_3 (m.d 1 2) (by simp) with h14301 | h14301
                            · linarith only [h0, h14301, hlam]
                            · linarith only [h14160, h14301, hlam]
                          · linarith only [h14300, hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          rcases p14297_3 (m.d 0 2) (by simp) with h14305 | h14305
                          · rcases p14297_3 (m.d 1 2) (by simp) with h14306 | h14306
                            · linarith only [h0, h14306, hlam]
                            · linarith only [h14161, h14306, hlam]
                          · linarith only [h14305, hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          rcases p14297_3 (m.d 0 2) (by simp) with h14310 | h14310
                          · rcases p14297_3 (m.d 1 2) (by simp) with h14311 | h14311
                            · linarith only [h0, h14311, hlam]
                            · linarith only [h14162, h14311, hlam]
                          · linarith only [h14310, hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h0, hlam, p14297_1]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          rcases p14297_3 (m.d 0 2) (by simp) with h14317 | h14317
                          · rcases p14297_3 (m.d 1 2) (by simp) with h14318 | h14318
                            · rcases p14297_3 (m.d 2 3) (by simp) with h14319 | h14319
                              · linarith only [h14319, hlam, p14297_0]
                              · rcases p14297_3 (m.d 2 4) (by simp) with h14321 | h14321
                                · linarith only [h14161, h14321, hlam]
                                · linarith only [h14168, h14321, hlam]
                            · linarith only [h14318, hlam, p14297_0]
                          · linarith only [h14317, h4, hlam]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h0, h14172, hc01, hc45, hlam, hphi, ht0b, ht5b, p14297_1]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          rcases p14297_3 (m.d 0 2) (by simp) with h14327 | h14327
                          · rcases p14297_3 (m.d 1 2) (by simp) with h14328 | h14328
                            · rcases p14297_3 (m.d 2 3) (by simp) with h14329 | h14329
                              · linarith only [h14160, h14329, hlam]
                              · rcases p14297_3 (m.d 2 4) (by simp) with h14331 | h14331
                                · linarith only [h14161, h14331, hlam]
                                · linarith only [h14172, h14331, hlam]
                            · linarith only [h14328, hlam, p14297_0]
                          · linarith only [h14327, h6, hlam]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h4, hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h14160, hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h14168, hlam, p14297_1]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h14170, hlam, p14297_1]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h5, hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h14161, hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h0, h14161, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14297_1]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h0, h14161, hc01, hc25, hlam, hphi, ht0b, ht5b, p14297_1]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h6, hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h14162, hlam, p14297_0]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h0, h14162, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14297_1]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [h14172, hlam, p14297_1]
                        · have p14297_0 := h14297c.1
                          have p14297_1 := h14297c.2.1
                          have p14297_2 := h14297c.2.2.1
                          have p14297_3 := h14297c.2.2.2
                          linarith only [hlam, p14297_0]
                  · linarith only [h14167, h14236, hlam]
              · linarith only [h14162, h14233, hlam]
            · linarith only [h14232, h3, hlam]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [h3, hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [h14162, hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            rcases p14174_3 (m.d 0 1) (by simp) with h14356 | h14356
            · rcases p14174_3 (m.d 1 2) (by simp) with h14357 | h14357
              · rcases p14174_3 (m.d 1 3) (by simp) with h14358 | h14358
                · linarith only [h14165, h14358, hlam]
                · rcases p14174_3 (m.d 1 4) (by simp) with h14360 | h14360
                  · rcases p14174_3 (m.d 1 5) (by simp) with h14361 | h14361
                    · rcases h1emax with h14362 | h14362 | h14362 | h14362 | h14362
                      · linarith only [h0, h14161, h14362, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h14160, h14161, h14167, h14362, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14174_1]
                      · rcases h2bigk with h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c | h14365c
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h0, h14160, h14161, h14167, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14174_1, p14365_1]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          rcases p14365_3 (m.d 0 2) (by simp) with h14368 | h14368
                          · rcases p14365_3 (m.d 1 2) (by simp) with h14369 | h14369
                            · linarith only [h0, h14369, hlam]
                            · linarith only [h14160, h14369, hlam]
                          · linarith only [h14368, hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          rcases p14365_3 (m.d 0 2) (by simp) with h14373 | h14373
                          · rcases p14365_3 (m.d 1 2) (by simp) with h14374 | h14374
                            · linarith only [h0, h14374, hlam]
                            · linarith only [h14161, h14374, hlam]
                          · linarith only [h14373, hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          rcases p14365_3 (m.d 0 2) (by simp) with h14378 | h14378
                          · rcases p14365_3 (m.d 1 2) (by simp) with h14379 | h14379
                            · linarith only [h0, h14379, hlam]
                            · linarith only [h14162, h14379, hlam]
                          · linarith only [h14378, hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h0, hlam, p14365_1]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          rcases p14365_3 (m.d 0 2) (by simp) with h14385 | h14385
                          · rcases p14365_3 (m.d 1 2) (by simp) with h14386 | h14386
                            · rcases p14365_3 (m.d 2 3) (by simp) with h14387 | h14387
                              · linarith only [h14387, hlam, p14365_0]
                              · rcases p14365_3 (m.d 2 4) (by simp) with h14389 | h14389
                                · linarith only [h14161, h14389, hlam]
                                · linarith only [h14168, h14389, hlam]
                            · linarith only [h14386, hlam, p14365_0]
                          · linarith only [h14385, h4, hlam]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h0, h14172, hc01, hc45, hlam, hphi, ht0b, ht5b, p14365_1]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          rcases p14365_3 (m.d 0 2) (by simp) with h14395 | h14395
                          · rcases p14365_3 (m.d 1 2) (by simp) with h14396 | h14396
                            · rcases p14365_3 (m.d 2 3) (by simp) with h14397 | h14397
                              · linarith only [h14160, h14397, hlam]
                              · rcases p14365_3 (m.d 2 4) (by simp) with h14399 | h14399
                                · linarith only [h14161, h14399, hlam]
                                · linarith only [h14172, h14399, hlam]
                            · linarith only [h14396, hlam, p14365_0]
                          · linarith only [h14395, h6, hlam]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h4, hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h14160, hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h14168, hlam, p14365_1]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h14170, hlam, p14365_1]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h5, hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h14161, hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h0, h14161, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14365_1]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h0, h14161, h14170, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14365_1]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h6, hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h14162, hlam, p14365_0]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h0, h14162, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14365_1]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [h14172, hlam, p14365_1]
                        · have p14365_0 := h14365c.1
                          have p14365_1 := h14365c.2.1
                          have p14365_2 := h14365c.2.2.1
                          have p14365_3 := h14365c.2.2.2
                          linarith only [hlam, p14365_0]
                      · linarith only [h14160, h14167, h14362, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14174_1]
                      · linarith only [h14160, h14362, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14174_1]
                    · linarith only [h14165, h14361, hlam]
                  · linarith only [h14163, h14360, hlam]
              · linarith only [h14160, h14357, hlam]
            · linarith only [h1, h14356, hlam]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [h14167, hlam, p14174_0]
          · have p14174_0 := h14174c.1
            have p14174_1 := h14174c.2.1
            have p14174_2 := h14174c.2.2.1
            have p14174_3 := h14174c.2.2.2
            linarith only [hlam, p14174_0]
        · linarith only [h14159, h14173, h7, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h14428 | h14428
        · rcases h1bigk with h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c | h14429c
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h14161, h14167, h14168, h14172, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14429_1]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            rcases p14429_3 (m.d 0 1) (by simp) with h14432 | h14432
            · rcases p14429_3 (m.d 1 2) (by simp) with h14433 | h14433
              · linarith only [h0, h14433, hlam]
              · linarith only [h14160, h14433, hlam]
            · linarith only [h14432, hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h14167, h14168, h14172, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14429_1]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            rcases p14429_3 (m.d 0 1) (by simp) with h14438 | h14438
            · rcases p14429_3 (m.d 1 2) (by simp) with h14439 | h14439
              · linarith only [h0, h14439, hlam]
              · linarith only [h14162, h14439, hlam]
            · linarith only [h14438, hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h0, hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            rcases p14429_3 (m.d 0 1) (by simp) with h14445 | h14445
            · rcases p14429_3 (m.d 1 2) (by simp) with h14446 | h14446
              · rcases p14429_3 (m.d 1 3) (by simp) with h14447 | h14447
                · linarith only [h14160, h14447, hlam]
                · rcases p14429_3 (m.d 1 4) (by simp) with h14449 | h14449
                  · linarith only [h14161, h14449, hlam]
                  · linarith only [h14163, h14449, hlam]
              · linarith only [h14160, h14446, hlam]
            · linarith only [h1, h14445, hlam]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h0, h14167, h14168, h14172, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14429_1]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h0, h14167, h14168, h14172, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14429_1]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h1, hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h14160, hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h14163, hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h14165, hlam, p14429_1]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h2, hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h14161, hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            rcases p14429_3 (m.d 0 1) (by simp) with h14463 | h14463
            · rcases p14429_3 (m.d 1 2) (by simp) with h14464 | h14464
              · rcases p14429_3 (m.d 1 3) (by simp) with h14465 | h14465
                · linarith only [h14163, h14465, hlam]
                · rcases p14429_3 (m.d 1 4) (by simp) with h14467 | h14467
                  · rcases p14429_3 (m.d 1 5) (by simp) with h14468 | h14468
                    · linarith only [h14167, h14468, hlam]
                    · linarith only [h14165, h14468, hlam]
                  · linarith only [h14163, h14467, hlam]
              · linarith only [h14160, h14464, hlam]
            · linarith only [h1, h14463, hlam]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h14167, h14168, h14172, h2, h7, hc23, hc34, hlam, hphi, p14429_1]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h3, hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h14162, hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            rcases p14429_3 (m.d 0 1) (by simp) with h14478 | h14478
            · rcases p14429_3 (m.d 1 2) (by simp) with h14479 | h14479
              · rcases p14429_3 (m.d 1 3) (by simp) with h14480 | h14480
                · linarith only [h14165, h14480, hlam]
                · rcases p14429_3 (m.d 1 4) (by simp) with h14482 | h14482
                  · rcases p14429_3 (m.d 1 5) (by simp) with h14483 | h14483
                    · rcases h1emax with h14484 | h14484 | h14484 | h14484 | h14484
                      · linarith only [h0, h14161, h14167, h14484, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14429_1]
                      · linarith only [h14160, h14161, h14167, h14484, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14429_1]
                      · rcases h2bigk with h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c | h14487c
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h14160, h14161, h14167, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14429_1, p14487_1]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          rcases p14487_3 (m.d 0 2) (by simp) with h14490 | h14490
                          · rcases p14487_3 (m.d 1 2) (by simp) with h14491 | h14491
                            · linarith only [h0, h14491, hlam]
                            · linarith only [h14160, h14491, hlam]
                          · linarith only [h14490, hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          rcases p14487_3 (m.d 0 2) (by simp) with h14495 | h14495
                          · rcases p14487_3 (m.d 1 2) (by simp) with h14496 | h14496
                            · linarith only [h0, h14496, hlam]
                            · linarith only [h14161, h14496, hlam]
                          · linarith only [h14495, hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          rcases p14487_3 (m.d 0 2) (by simp) with h14500 | h14500
                          · rcases p14487_3 (m.d 1 2) (by simp) with h14501 | h14501
                            · linarith only [h0, h14501, hlam]
                            · linarith only [h14162, h14501, hlam]
                          · linarith only [h14500, hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h0, hlam, p14487_1]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          rcases p14487_3 (m.d 0 2) (by simp) with h14507 | h14507
                          · rcases p14487_3 (m.d 1 2) (by simp) with h14508 | h14508
                            · rcases p14487_3 (m.d 2 3) (by simp) with h14509 | h14509
                              · linarith only [h14509, hlam, p14487_0]
                              · rcases p14487_3 (m.d 2 4) (by simp) with h14511 | h14511
                                · linarith only [h14161, h14511, hlam]
                                · linarith only [h14168, h14511, hlam]
                            · linarith only [h14508, hlam, p14487_0]
                          · linarith only [h14507, h4, hlam]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          rcases p14487_3 (m.d 0 2) (by simp) with h14516 | h14516
                          · rcases p14487_3 (m.d 1 2) (by simp) with h14517 | h14517
                            · rcases p14487_3 (m.d 2 3) (by simp) with h14518 | h14518
                              · linarith only [h14160, h14518, hlam]
                              · rcases p14487_3 (m.d 2 4) (by simp) with h14520 | h14520
                                · linarith only [h14520, hlam, p14487_0]
                                · rcases p14487_3 (m.d 2 5) (by simp) with h14522 | h14522
                                  · linarith only [h14162, h14522, hlam]
                                  · linarith only [h14172, h14522, hlam]
                            · linarith only [h14517, hlam, p14487_0]
                          · linarith only [h14516, h5, hlam]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          rcases p14487_3 (m.d 0 2) (by simp) with h14527 | h14527
                          · rcases p14487_3 (m.d 1 2) (by simp) with h14528 | h14528
                            · rcases p14487_3 (m.d 2 3) (by simp) with h14529 | h14529
                              · linarith only [h14160, h14529, hlam]
                              · rcases p14487_3 (m.d 2 4) (by simp) with h14531 | h14531
                                · linarith only [h14161, h14531, hlam]
                                · rcases p14487_3 (m.d 2 5) (by simp) with h14533 | h14533
                                  · linarith only [h14533, hlam, p14487_0]
                                  · rcases h4bigk with h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c | h14535c
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [hlam, p14535_0]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14160, h14167, h7, hc23, hc34, hlam, hphi, p14429_1, p14535_1]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      rcases p14535_3 (m.d 0 4) (by simp) with h14538 | h14538
                                      · rcases p14535_3 (m.d 1 4) (by simp) with h14539 | h14539
                                        · linarith only [h14539, h2, hlam]
                                        · linarith only [h14161, h14539, hlam]
                                      · linarith only [h14538, h5, hlam]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h7, hlam, p14535_1]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14168, h14172, h7, hc23, hc34, hlam, hphi, p14535_1]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h2, hlam, p14535_0]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [hlam, p14535_0]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      rcases p14535_3 (m.d 0 4) (by simp) with h14547 | h14547
                                      · rcases p14535_3 (m.d 1 4) (by simp) with h14548 | h14548
                                        · rcases p14535_3 (m.d 2 4) (by simp) with h14549 | h14549
                                          · linarith only [h14161, h14549, hlam]
                                          · rcases p14535_3 (m.d 3 4) (by simp) with h14551 | h14551
                                            · rcases p14535_3 (m.d 4 5) (by simp) with h14552 | h14552
                                              · linarith only [h14167, h14552, hlam]
                                              · linarith only [h14172, h14552, hlam]
                                            · linarith only [h14168, h14551, hlam]
                                        · linarith only [h14161, h14548, hlam]
                                      · linarith only [h14547, h5, hlam]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14163, hlam, p14535_1]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14168, h14172, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14535_1]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h5, hlam, p14535_0]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14161, hlam, p14535_0]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [hlam, p14535_0]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14168, hlam, p14535_1]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14172, hlam, p14535_0]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14159, h14160, h3, hc23, hc34, hlam, hphi, p14429_1, p14535_1]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14167, h14168, h14172, hc23, hc34, hlam, hphi, p14535_1]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      rcases p14535_3 (m.d 0 4) (by simp) with h14567 | h14567
                                      · linarith only [h14567, h7, hlam]
                                      · linarith only [h14567, h5, hlam]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [hlam, p14535_0]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14168, h14172, hc23, hc34, hlam, hphi, p14535_1]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14159, hlam, p14535_0]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14167, hlam, p14535_0]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14159, h14168, h7, hc23, hc34, hlam, hphi, p14535_1]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [h14428, hlam, p14535_0]
                                    · have p14535_0 := h14535c.1
                                      have p14535_1 := h14535c.2.1
                                      have p14535_2 := h14535c.2.2.1
                                      have p14535_3 := h14535c.2.2.2
                                      linarith only [hlam, p14535_0]
                            · linarith only [h14528, hlam, p14487_0]
                          · linarith only [h14527, h6, hlam]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h4, hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h14160, hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h14168, hlam, p14487_1]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h14170, hlam, p14487_1]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h5, hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h14161, hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h0, h14161, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14487_1]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h14172, hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h6, hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h14162, hlam, p14487_0]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h0, h14162, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14487_1]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [h0, h14161, h14167, h14172, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p14487_1]
                        · have p14487_0 := h14487c.1
                          have p14487_1 := h14487c.2.1
                          have p14487_2 := h14487c.2.2.1
                          have p14487_3 := h14487c.2.2.2
                          linarith only [hlam, p14487_0]
                      · linarith only [h14160, h14167, h14484, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14429_1]
                      · linarith only [h14160, h14484, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14429_1]
                    · linarith only [h14165, h14483, hlam]
                  · linarith only [h14163, h14482, hlam]
              · linarith only [h14160, h14479, hlam]
            · linarith only [h1, h14478, hlam]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [h14167, hlam, p14429_0]
          · have p14429_0 := h14429c.1
            have p14429_1 := h14429c.2.1
            have p14429_2 := h14429c.2.2.1
            have p14429_3 := h14429c.2.2.2
            linarith only [hlam, p14429_0]
        · linarith only [h14167, h14428, h2, h7, hlam]

end R2N4
