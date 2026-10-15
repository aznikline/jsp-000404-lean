import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2031 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2186 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2187 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h2bigk := hb2.1
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
  rcases m.htr 1 4 5 (by decide) (by decide) with h2188 | h2188
  · rcases m.htr 2 3 4 (by decide) (by decide) with h2189 | h2189
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2190 | h2190
      · rcases m.htr 2 4 5 (by decide) (by decide) with h2191 | h2191
        · rcases m.htr 3 4 5 (by decide) (by decide) with h2192 | h2192
          · rcases h2bigk with h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c | h2193c
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              rcases p2193_3 (m.d 0 2) (by simp) with h2195 | h2195
              · rcases p2193_3 (m.d 1 2) (by simp) with h2196 | h2196
                · linarith only [h0, h2196, hlam]
                · rcases p2193_3 (m.d 2 3) (by simp) with h2198 | h2198
                  · linarith only [h2198, h3, hlam]
                  · linarith only [h2198, h9, hlam]
              · linarith only [h0, h2195, hlam]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h0, h2186, h2192, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p2193_1]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              rcases p2193_3 (m.d 0 2) (by simp) with h2203 | h2203
              · rcases p2193_3 (m.d 1 2) (by simp) with h2204 | h2204
                · linarith only [h0, h2204, hlam]
                · rcases p2193_3 (m.d 2 3) (by simp) with h2206 | h2206
                  · linarith only [h2206, h3, hlam]
                  · linarith only [h2189, h2206, hlam]
              · linarith only [h2203, hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              rcases p2193_3 (m.d 0 2) (by simp) with h2210 | h2210
              · rcases p2193_3 (m.d 1 2) (by simp) with h2211 | h2211
                · linarith only [h0, h2211, hlam]
                · rcases p2193_3 (m.d 2 3) (by simp) with h2213 | h2213
                  · linarith only [h2213, h3, hlam]
                  · linarith only [h2190, h2213, hlam]
              · linarith only [h2210, hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h0, hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h9, hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h2031, h2191, hlam, p2193_1]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h2031, hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h3, hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              rcases p2193_3 (m.d 0 2) (by simp) with h2223 | h2223
              · rcases p2193_3 (m.d 1 2) (by simp) with h2224 | h2224
                · linarith only [h2224, hlam, p2193_0]
                · rcases p2193_3 (m.d 2 3) (by simp) with h2226 | h2226
                  · rcases p2193_3 (m.d 2 4) (by simp) with h2227 | h2227
                    · linarith only [h2189, h2227, hlam]
                    · linarith only [h2031, h2191, h2227, hlam]
                  · linarith only [h2226, hlam, p2193_0]
              · linarith only [h0, h2223, hlam]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h2031, h2191, hc12, hc23, hlam, hphi, p2193_1]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h0, h2031, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2193_1]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h4, hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              rcases p2193_3 (m.d 0 2) (by simp) with h2236 | h2236
              · rcases p2193_3 (m.d 1 2) (by simp) with h2237 | h2237
                · linarith only [h2237, hlam, p2193_0]
                · rcases p2193_3 (m.d 2 3) (by simp) with h2239 | h2239
                  · rcases p2193_3 (m.d 2 4) (by simp) with h2240 | h2240
                    · rcases p2193_3 (m.d 2 5) (by simp) with h2241 | h2241
                      · linarith only [h2191, h2241, hlam]
                      · linarith only [h2031, h2241, hlam]
                    · linarith only [h2240, hlam, p2193_0]
                  · linarith only [h2239, h9, hlam]
              · linarith only [h0, h2236, hlam]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h2189, hlam, p2193_1]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h2031, hc12, hc24, hlam, hphi, p2193_1]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h5, hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              rcases p2193_3 (m.d 0 2) (by simp) with h2251 | h2251
              · rcases p2193_3 (m.d 1 2) (by simp) with h2252 | h2252
                · linarith only [h2252, hlam, p2193_0]
                · rcases p2193_3 (m.d 2 3) (by simp) with h2254 | h2254
                  · rcases p2193_3 (m.d 2 4) (by simp) with h2255 | h2255
                    · rcases p2193_3 (m.d 2 5) (by simp) with h2256 | h2256
                      · rcases h3bigk with h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c | h2257c
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h0, h2186, h2192, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h0, h2186, h2192, h3, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          rcases p2257_3 (m.d 0 3) (by simp) with h2261 | h2261
                          · rcases p2257_3 (m.d 1 3) (by simp) with h2262 | h2262
                            · linarith only [h1, h2262, hlam]
                            · linarith only [h2186, h2262, hlam]
                          · linarith only [h2261, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          rcases p2257_3 (m.d 0 3) (by simp) with h2266 | h2266
                          · rcases p2257_3 (m.d 1 3) (by simp) with h2267 | h2267
                            · linarith only [h1, h2267, hlam]
                            · linarith only [h2187, h2267, hlam]
                          · linarith only [h2266, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h1, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h9, hlam, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h1, h2192, hc01, hc45, hlam, hphi, ht0b, ht5b, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          rcases p2257_3 (m.d 0 3) (by simp) with h2275 | h2275
                          · rcases p2257_3 (m.d 1 3) (by simp) with h2276 | h2276
                            · rcases p2257_3 (m.d 2 3) (by simp) with h2277 | h2277
                              · rcases p2257_3 (m.d 3 4) (by simp) with h2278 | h2278
                                · linarith only [h2186, h2278, hlam]
                                · linarith only [h2192, h2278, hlam]
                              · linarith only [h2190, h2277, hlam]
                            · linarith only [h2276, hlam, p2257_0]
                          · linarith only [h2275, h7, hlam]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h3, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h0, h2186, h2192, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h0, h2192, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          rcases p2257_3 (m.d 0 3) (by simp) with h2288 | h2288
                          · rcases p2257_3 (m.d 1 3) (by simp) with h2289 | h2289
                            · linarith only [h2289, h9, hlam]
                            · linarith only [h2187, h2289, hlam]
                          · linarith only [h2288, h7, hlam]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h6, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2186, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2189, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h1, h2186, hc01, hc35, hlam, hphi, ht0b, ht5b, p2257_1]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h7, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2187, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2190, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [h2192, hlam, p2257_0]
                        · have p2257_0 := h2257c.1
                          have p2257_1 := h2257c.2.1
                          have p2257_2 := h2257c.2.2.1
                          have p2257_3 := h2257c.2.2.2
                          linarith only [hlam, p2257_0]
                      · linarith only [h2256, hlam, p2193_0]
                    · linarith only [h2191, h2255, hlam, p2193_1]
                  · linarith only [h2254, h9, hlam]
              · linarith only [h0, h2251, hlam]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h2190, hlam, p2193_1]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [h2191, hlam, p2193_0]
            · have p2193_0 := h2193c.1
              have p2193_1 := h2193c.2.1
              have p2193_2 := h2193c.2.2.1
              have p2193_3 := h2193c.2.2.2
              linarith only [hlam, p2193_0]
          · rcases h2bigk with h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c | h2310c
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [hlam, p2310_0]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              rcases p2310_3 (m.d 0 2) (by simp) with h2312 | h2312
              · rcases p2310_3 (m.d 1 2) (by simp) with h2313 | h2313
                · linarith only [h0, h2313, hlam]
                · rcases p2310_3 (m.d 2 3) (by simp) with h2315 | h2315
                  · linarith only [h2315, h3, hlam]
                  · linarith only [h2315, h9, hlam]
              · linarith only [h0, h2312, hlam]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h0, h2186, h2188, h2192, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2310_1]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h0, h2191, h2192, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2310_1]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              rcases p2310_3 (m.d 0 2) (by simp) with h2321 | h2321
              · rcases p2310_3 (m.d 1 2) (by simp) with h2322 | h2322
                · linarith only [h0, h2322, hlam]
                · rcases p2310_3 (m.d 2 3) (by simp) with h2324 | h2324
                  · linarith only [h2324, h3, hlam]
                  · linarith only [h2190, h2324, hlam]
              · linarith only [h2321, hlam, p2310_0]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h0, hlam, p2310_0]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [hlam, p2310_0]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h9, hlam, p2310_0]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h2191, h2192, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2310_1]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h2031, hlam, p2310_0]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h3, hlam, p2310_0]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              rcases p2310_3 (m.d 0 2) (by simp) with h2334 | h2334
              · rcases p2310_3 (m.d 1 2) (by simp) with h2335 | h2335
                · linarith only [h2335, hlam, p2310_0]
                · rcases p2310_3 (m.d 2 3) (by simp) with h2337 | h2337
                  · rcases p2310_3 (m.d 2 4) (by simp) with h2338 | h2338
                    · linarith only [h2189, h2338, hlam]
                    · linarith only [h2031, h2191, h2338, hlam]
                  · linarith only [h2337, hlam, p2310_0]
              · linarith only [h0, h2334, hlam]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [hlam, p2310_0]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h0, h2031, h2191, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2310_1]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h0, h2031, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2310_1]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h4, hlam, p2310_0]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              rcases p2310_3 (m.d 0 2) (by simp) with h2347 | h2347
              · rcases p2310_3 (m.d 1 2) (by simp) with h2348 | h2348
                · linarith only [h2348, hlam, p2310_0]
                · rcases p2310_3 (m.d 2 3) (by simp) with h2350 | h2350
                  · rcases p2310_3 (m.d 2 4) (by simp) with h2351 | h2351
                    · rcases p2310_3 (m.d 2 5) (by simp) with h2352 | h2352
                      · linarith only [h2191, h2352, hlam]
                      · linarith only [h2031, h2352, hlam]
                    · linarith only [h2351, hlam, p2310_0]
                  · linarith only [h2350, h9, hlam]
              · linarith only [h0, h2347, hlam]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h2189, hlam, p2310_1]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [hlam, p2310_0]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h2031, hc12, hc24, hlam, hphi, p2310_1]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h5, hlam, p2310_0]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              rcases p2310_3 (m.d 0 2) (by simp) with h2362 | h2362
              · rcases p2310_3 (m.d 1 2) (by simp) with h2363 | h2363
                · linarith only [h2363, hlam, p2310_0]
                · rcases p2310_3 (m.d 2 3) (by simp) with h2365 | h2365
                  · rcases p2310_3 (m.d 2 4) (by simp) with h2366 | h2366
                    · rcases p2310_3 (m.d 2 5) (by simp) with h2367 | h2367
                      · rcases h3bigk with h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c | h2368c
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h0, h2186, h2188, h2192, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2368_1]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h0, h2186, h2188, h2192, h3, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2368_1]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          rcases p2368_3 (m.d 0 3) (by simp) with h2372 | h2372
                          · rcases p2368_3 (m.d 1 3) (by simp) with h2373 | h2373
                            · linarith only [h1, h2373, hlam]
                            · linarith only [h2186, h2373, hlam]
                          · linarith only [h2372, hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          rcases p2368_3 (m.d 0 3) (by simp) with h2377 | h2377
                          · rcases p2368_3 (m.d 1 3) (by simp) with h2378 | h2378
                            · linarith only [h1, h2378, hlam]
                            · linarith only [h2187, h2378, hlam]
                          · linarith only [h2377, hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h1, hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h9, hlam, p2368_1]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          rcases p2368_3 (m.d 0 3) (by simp) with h2385 | h2385
                          · rcases p2368_3 (m.d 1 3) (by simp) with h2386 | h2386
                            · rcases p2368_3 (m.d 2 3) (by simp) with h2387 | h2387
                              · rcases p2368_3 (m.d 3 4) (by simp) with h2388 | h2388
                                · linarith only [h2388, hlam, p2368_0]
                                · rcases p2368_3 (m.d 3 5) (by simp) with h2390 | h2390
                                  · linarith only [h2187, h2390, hlam]
                                  · linarith only [h2192, h2390, hlam]
                              · linarith only [h2189, h2387, hlam]
                            · linarith only [h2386, hlam, p2368_0]
                          · linarith only [h2385, h6, hlam]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          rcases p2368_3 (m.d 0 3) (by simp) with h2396 | h2396
                          · rcases p2368_3 (m.d 1 3) (by simp) with h2397 | h2397
                            · rcases p2368_3 (m.d 2 3) (by simp) with h2398 | h2398
                              · rcases p2368_3 (m.d 3 4) (by simp) with h2399 | h2399
                                · linarith only [h2186, h2399, hlam]
                                · rcases p2368_3 (m.d 3 5) (by simp) with h2401 | h2401
                                  · linarith only [h2401, hlam, p2368_0]
                                  · rcases h5bigk with h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [hlam, p2403_0]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h2188, h2192, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2403_1]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h0, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2310_1, p2403_1]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      rcases p2403_3 (m.d 0 5) (by simp) with h2407 | h2407
                                      · rcases p2403_3 (m.d 1 5) (by simp) with h2408 | h2408
                                        · linarith only [h2, h2408, hlam]
                                        · linarith only [h2187, h2408, hlam]
                                      · linarith only [h2407, h7, hlam]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h2192, h6, h8, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2403_1]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h2, hlam, p2403_0]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [hlam, p2403_0]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h2031, hlam, p2403_0]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h2, h2192, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2403_1]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h2186, h2188, h2192, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2403_1]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h5, hlam, p2403_1]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h0, h2189, h2191, h3, hc01, hc15, hlam, hphi, ht0b, ht5b, p2403_1]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [hlam, p2403_0]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h0, h2189, h2191, h2192, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2403_1]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h0, h2189, h2191, h2192, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2403_1]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h7, hlam, p2403_0]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h2187, hlam, p2403_0]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h2190, hlam, p2403_0]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [hlam, p2403_0]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h2192, hlam, p2403_1]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h8, hlam, p2403_0]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h2188, hlam, p2403_0]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h2191, hlam, p2403_0]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [h2192, hc34, hc45, hlam, hphi, p2403_1]
                                    · have p2403_0 := h2403c.1
                                      have p2403_1 := h2403c.2.1
                                      have p2403_2 := h2403c.2.2.1
                                      have p2403_3 := h2403c.2.2.2
                                      linarith only [hlam, p2403_0]
                              · linarith only [h2190, h2398, hlam]
                            · linarith only [h2397, hlam, p2368_0]
                          · linarith only [h2396, h7, hlam]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h3, hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h0, h2186, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2368_1]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          rcases p2368_3 (m.d 0 3) (by simp) with h2439 | h2439
                          · rcases p2368_3 (m.d 1 3) (by simp) with h2440 | h2440
                            · linarith only [h2440, h9, hlam]
                            · linarith only [h2186, h2440, hlam]
                          · linarith only [h2439, h6, hlam]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          rcases p2368_3 (m.d 0 3) (by simp) with h2444 | h2444
                          · rcases p2368_3 (m.d 1 3) (by simp) with h2445 | h2445
                            · linarith only [h2445, h9, hlam]
                            · linarith only [h2187, h2445, hlam]
                          · linarith only [h2444, h7, hlam]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h6, hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h2186, hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h2189, hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h2192, hlam, p2368_1]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h7, hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h2187, hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h2190, hlam, p2368_0]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [h1, h2187, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2368_1]
                        · have p2368_0 := h2368c.1
                          have p2368_1 := h2368c.2.1
                          have p2368_2 := h2368c.2.2.1
                          have p2368_3 := h2368c.2.2.2
                          linarith only [hlam, p2368_0]
                      · linarith only [h2367, hlam, p2310_0]
                    · linarith only [h2191, h2366, hlam, p2310_1]
                  · linarith only [h2365, h9, hlam]
              · linarith only [h0, h2362, hlam]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h2190, hlam, p2310_1]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [h2191, hlam, p2310_0]
            · have p2310_0 := h2310c.1
              have p2310_1 := h2310c.2.1
              have p2310_2 := h2310c.2.2.1
              have p2310_3 := h2310c.2.2.2
              linarith only [hlam, p2310_0]
        · linarith only [h2031, h2188, h2191, hlam]
      · linarith only [h2187, h2190, h9, hlam]
    · linarith only [h2186, h2189, h9, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h2469 | h2469
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2470 | h2470
      · rcases m.htr 2 4 5 (by decide) (by decide) with h2471 | h2471
        · rcases m.htr 3 4 5 (by decide) (by decide) with h2472 | h2472
          · linarith only [h2186, h2188, h2472, hlam]
          · rcases h2bigk with h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c | h2474c
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [hlam, p2474_0]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              rcases p2474_3 (m.d 0 2) (by simp) with h2476 | h2476
              · rcases p2474_3 (m.d 1 2) (by simp) with h2477 | h2477
                · linarith only [h0, h2477, hlam]
                · rcases p2474_3 (m.d 2 3) (by simp) with h2479 | h2479
                  · linarith only [h2479, h3, hlam]
                  · linarith only [h2479, h9, hlam]
              · linarith only [h0, h2476, hlam]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h0, h2188, h2469, h2471, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2474_1]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h0, h2186, h2188, h2471, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2474_1]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              rcases p2474_3 (m.d 0 2) (by simp) with h2485 | h2485
              · rcases p2474_3 (m.d 1 2) (by simp) with h2486 | h2486
                · linarith only [h0, h2486, hlam]
                · rcases p2474_3 (m.d 2 3) (by simp) with h2488 | h2488
                  · linarith only [h2488, h3, hlam]
                  · linarith only [h2470, h2488, hlam]
              · linarith only [h2485, hlam, p2474_0]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h0, hlam, p2474_0]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [hlam, p2474_0]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h9, hlam, p2474_0]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h2186, h2188, h2471, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2474_1]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h2031, hlam, p2474_0]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h3, hlam, p2474_0]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              rcases p2474_3 (m.d 0 2) (by simp) with h2498 | h2498
              · rcases p2474_3 (m.d 1 2) (by simp) with h2499 | h2499
                · linarith only [h2499, hlam, p2474_0]
                · rcases p2474_3 (m.d 2 3) (by simp) with h2501 | h2501
                  · rcases p2474_3 (m.d 2 4) (by simp) with h2502 | h2502
                    · linarith only [h2469, h2502, hlam]
                    · linarith only [h2186, h2188, h2471, h2502, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2474_1]
                  · linarith only [h2501, hlam, p2474_0]
              · linarith only [h0, h2498, hlam]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [hlam, p2474_0]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h2186, h2188, h2471, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2474_1]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h0, h2031, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2474_1]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h4, hlam, p2474_0]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              rcases p2474_3 (m.d 0 2) (by simp) with h2511 | h2511
              · rcases p2474_3 (m.d 1 2) (by simp) with h2512 | h2512
                · linarith only [h2512, hlam, p2474_0]
                · rcases p2474_3 (m.d 2 3) (by simp) with h2514 | h2514
                  · rcases p2474_3 (m.d 2 4) (by simp) with h2515 | h2515
                    · rcases p2474_3 (m.d 2 5) (by simp) with h2516 | h2516
                      · linarith only [h2471, h2516, hlam]
                      · linarith only [h2031, h2516, hlam]
                    · linarith only [h2515, hlam, p2474_0]
                  · linarith only [h2514, h9, hlam]
              · linarith only [h0, h2511, hlam]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h2469, hlam, p2474_1]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [hlam, p2474_0]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h2031, hc12, hc24, hlam, hphi, p2474_1]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h5, hlam, p2474_0]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              rcases p2474_3 (m.d 0 2) (by simp) with h2526 | h2526
              · rcases p2474_3 (m.d 1 2) (by simp) with h2527 | h2527
                · linarith only [h2527, hlam, p2474_0]
                · rcases p2474_3 (m.d 2 3) (by simp) with h2529 | h2529
                  · rcases p2474_3 (m.d 2 4) (by simp) with h2530 | h2530
                    · rcases p2474_3 (m.d 2 5) (by simp) with h2531 | h2531
                      · rcases h3bigk with h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c | h2532c
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          rcases p2532_3 (m.d 0 3) (by simp) with h2534 | h2534
                          · rcases p2532_3 (m.d 1 3) (by simp) with h2535 | h2535
                            · linarith only [h1, h2535, hlam]
                            · rcases p2532_3 (m.d 2 3) (by simp) with h2537 | h2537
                              · linarith only [h2537, h3, hlam]
                              · linarith only [h2537, h9, hlam]
                          · linarith only [h1, h2534, hlam]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h0, h2470, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2474_1, p2532_1]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          rcases p2532_3 (m.d 0 3) (by simp) with h2542 | h2542
                          · rcases p2532_3 (m.d 1 3) (by simp) with h2543 | h2543
                            · linarith only [h1, h2543, hlam]
                            · linarith only [h2186, h2543, hlam]
                          · linarith only [h2542, hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          rcases p2532_3 (m.d 0 3) (by simp) with h2547 | h2547
                          · rcases p2532_3 (m.d 1 3) (by simp) with h2548 | h2548
                            · linarith only [h1, h2548, hlam]
                            · linarith only [h2187, h2548, hlam]
                          · linarith only [h2547, hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h1, hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h9, hlam, p2532_1]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          rcases p2532_3 (m.d 0 3) (by simp) with h2555 | h2555
                          · rcases p2532_3 (m.d 1 3) (by simp) with h2556 | h2556
                            · rcases p2532_3 (m.d 2 3) (by simp) with h2557 | h2557
                              · rcases p2532_3 (m.d 3 4) (by simp) with h2558 | h2558
                                · linarith only [h2558, hlam, p2532_0]
                                · rcases p2532_3 (m.d 3 5) (by simp) with h2560 | h2560
                                  · linarith only [h2187, h2560, hlam]
                                  · linarith only [h2472, h2560, hlam]
                              · linarith only [h2469, h2557, hlam]
                            · linarith only [h2556, hlam, p2532_0]
                          · linarith only [h2555, h6, hlam]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          rcases p2532_3 (m.d 0 3) (by simp) with h2566 | h2566
                          · rcases p2532_3 (m.d 1 3) (by simp) with h2567 | h2567
                            · rcases p2532_3 (m.d 2 3) (by simp) with h2568 | h2568
                              · rcases p2532_3 (m.d 3 4) (by simp) with h2569 | h2569
                                · linarith only [h2186, h2569, hlam]
                                · rcases p2532_3 (m.d 3 5) (by simp) with h2571 | h2571
                                  · linarith only [h2571, hlam, p2532_0]
                                  · rcases h5bigk with h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [hlam, p2573_0]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      rcases p2573_3 (m.d 0 5) (by simp) with h2575 | h2575
                                      · rcases p2573_3 (m.d 1 5) (by simp) with h2576 | h2576
                                        · linarith only [h2, h2576, hlam]
                                        · rcases p2573_3 (m.d 2 5) (by simp) with h2578 | h2578
                                          · linarith only [h2578, h5, hlam]
                                          · linarith only [h2031, h2578, hlam]
                                      · linarith only [h2, h2575, hlam]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2474_1, p2573_1]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      rcases p2573_3 (m.d 0 5) (by simp) with h2583 | h2583
                                      · rcases p2573_3 (m.d 1 5) (by simp) with h2584 | h2584
                                        · linarith only [h2, h2584, hlam]
                                        · linarith only [h2187, h2584, hlam]
                                      · linarith only [h2583, h7, hlam]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h0, h2188, h3, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2573_1]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h2, hlam, p2573_0]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [hlam, p2573_0]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h2031, hlam, p2573_0]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p2573_1]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h2188, hlam, p2573_1]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h5, hlam, p2573_1]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h0, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p2573_1]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [hlam, p2573_0]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h0, h2470, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p2573_1]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h0, h2186, h2188, h2469, h2471, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2573_1]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h7, hlam, p2573_0]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h2187, hlam, p2573_0]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h2470, hlam, p2573_0]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [hlam, p2573_0]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h2472, hlam, p2573_1]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h8, hlam, p2573_0]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h2031, hc12, hc45, hlam, hphi, ht23, ht34, p2573_1]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h2471, hlam, p2573_0]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [h0, h2469, h2471, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p2573_1]
                                    · have p2573_0 := h2573c.1
                                      have p2573_1 := h2573c.2.1
                                      have p2573_2 := h2573c.2.2.1
                                      have p2573_3 := h2573c.2.2.2
                                      linarith only [hlam, p2573_0]
                              · linarith only [h2470, h2568, hlam]
                            · linarith only [h2567, hlam, p2532_0]
                          · linarith only [h2566, h7, hlam]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h3, hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h0, h2186, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2532_1]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          rcases p2532_3 (m.d 0 3) (by simp) with h2615 | h2615
                          · rcases p2532_3 (m.d 1 3) (by simp) with h2616 | h2616
                            · linarith only [h2616, h9, hlam]
                            · linarith only [h2186, h2616, hlam]
                          · linarith only [h2615, h6, hlam]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          rcases p2532_3 (m.d 0 3) (by simp) with h2620 | h2620
                          · rcases p2532_3 (m.d 1 3) (by simp) with h2621 | h2621
                            · linarith only [h2621, h9, hlam]
                            · linarith only [h2187, h2621, hlam]
                          · linarith only [h2620, h7, hlam]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h6, hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h2186, hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h2469, hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h2472, hlam, p2532_1]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h7, hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h2187, hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h2470, hlam, p2532_0]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [h1, h2187, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2532_1]
                        · have p2532_0 := h2532c.1
                          have p2532_1 := h2532c.2.1
                          have p2532_2 := h2532c.2.2.1
                          have p2532_3 := h2532c.2.2.2
                          linarith only [hlam, p2532_0]
                      · linarith only [h2531, hlam, p2474_0]
                    · linarith only [h2471, h2530, hlam, p2474_1]
                  · linarith only [h2529, h9, hlam]
              · linarith only [h0, h2526, hlam]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h2470, hlam, p2474_1]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [h2471, hlam, p2474_0]
            · have p2474_0 := h2474c.1
              have p2474_1 := h2474c.2.1
              have p2474_2 := h2474c.2.2.1
              have p2474_3 := h2474c.2.2.2
              linarith only [hlam, p2474_0]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h2642 | h2642
          · linarith only [h0, h2186, h2471, h2642, h3, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases h2bigk with h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c | h2644c
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              rcases p2644_3 (m.d 0 2) (by simp) with h2646 | h2646
              · rcases p2644_3 (m.d 1 2) (by simp) with h2647 | h2647
                · linarith only [h0, h2647, hlam]
                · rcases p2644_3 (m.d 2 3) (by simp) with h2649 | h2649
                  · linarith only [h2649, h3, hlam]
                  · linarith only [h2649, h9, hlam]
              · linarith only [h0, h2646, hlam]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              rcases p2644_3 (m.d 0 2) (by simp) with h2653 | h2653
              · rcases p2644_3 (m.d 1 2) (by simp) with h2654 | h2654
                · linarith only [h0, h2654, hlam]
                · rcases p2644_3 (m.d 2 3) (by simp) with h2656 | h2656
                  · linarith only [h2656, hlam, p2644_0]
                  · rcases p2644_3 (m.d 2 4) (by simp) with h2658 | h2658
                    · linarith only [h2658, h4, hlam]
                    · rcases p2644_3 (m.d 2 5) (by simp) with h2660 | h2660
                      · linarith only [h2660, h5, hlam]
                      · rcases h3bigk with h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c | h2662c
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          rcases p2662_3 (m.d 0 3) (by simp) with h2664 | h2664
                          · rcases p2662_3 (m.d 1 3) (by simp) with h2665 | h2665
                            · linarith only [h1, h2665, hlam]
                            · rcases p2662_3 (m.d 2 3) (by simp) with h2667 | h2667
                              · linarith only [h2667, h3, hlam]
                              · linarith only [h2667, h9, hlam]
                          · linarith only [h1, h2664, hlam]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          rcases p2662_3 (m.d 0 3) (by simp) with h2671 | h2671
                          · rcases p2662_3 (m.d 1 3) (by simp) with h2672 | h2672
                            · linarith only [h1, h2672, hlam]
                            · rcases p2662_3 (m.d 2 3) (by simp) with h2674 | h2674
                              · linarith only [h2674, h3, hlam]
                              · rcases p2662_3 (m.d 3 4) (by simp) with h2676 | h2676
                                · linarith only [h2676, h6, hlam]
                                · rcases p2662_3 (m.d 3 5) (by simp) with h2678 | h2678
                                  · linarith only [h2678, h7, hlam]
                                  · rcases h5bigk with h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c | h2680c
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [hlam, p2680_0]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      rcases p2680_3 (m.d 0 5) (by simp) with h2682 | h2682
                                      · rcases p2680_3 (m.d 1 5) (by simp) with h2683 | h2683
                                        · linarith only [h2, h2683, hlam]
                                        · rcases p2680_3 (m.d 2 5) (by simp) with h2685 | h2685
                                          · linarith only [h2685, h5, hlam]
                                          · linarith only [h2031, h2685, hlam]
                                      · linarith only [h2, h2682, hlam]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h0, h2031, h3, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2680_1]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      rcases p2680_3 (m.d 0 5) (by simp) with h2690 | h2690
                                      · rcases p2680_3 (m.d 1 5) (by simp) with h2691 | h2691
                                        · linarith only [h2, h2691, hlam]
                                        · linarith only [h2187, h2691, hlam]
                                      · linarith only [h2690, h7, hlam]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h0, h2188, h3, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2680_1]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h2, hlam, p2680_0]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [hlam, p2680_0]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h2031, hlam, p2680_0]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p2680_1]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h2188, hlam, p2680_1]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h5, hlam, p2680_1]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h0, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p2680_1]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [hlam, p2680_0]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h0, h2470, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p2662_1, p2680_1]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h2471, hlam, p2680_1]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h7, hlam, p2680_0]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h2187, hlam, p2680_0]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h2470, hlam, p2680_0]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [hlam, p2680_0]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h2642, hlam, p2680_1]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h8, hlam, p2680_0]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h2031, hc12, hc45, hlam, hphi, ht23, ht34, p2680_1]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p2680_1]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p2680_1]
                                    · have p2680_0 := h2680c.1
                                      have p2680_1 := h2680c.2.1
                                      have p2680_2 := h2680c.2.2.1
                                      have p2680_3 := h2680c.2.2.2
                                      linarith only [hlam, p2680_0]
                          · linarith only [h2671, h3, hlam]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          rcases p2662_3 (m.d 0 3) (by simp) with h2717 | h2717
                          · rcases p2662_3 (m.d 1 3) (by simp) with h2718 | h2718
                            · linarith only [h1, h2718, hlam]
                            · linarith only [h2186, h2718, hlam]
                          · linarith only [h2717, hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          rcases p2662_3 (m.d 0 3) (by simp) with h2722 | h2722
                          · rcases p2662_3 (m.d 1 3) (by simp) with h2723 | h2723
                            · linarith only [h1, h2723, hlam]
                            · linarith only [h2187, h2723, hlam]
                          · linarith only [h2722, hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h1, hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h9, hlam, p2662_1]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h0, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2644_1, p2662_1]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h0, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p2644_1, p2662_1]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h3, hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2644_1, p2662_1]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2644_1, p2662_1]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht0b, ht5b, p2644_1, p2662_1]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h6, hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h2186, hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h2469, hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h2642, hlam, p2662_1]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h7, hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h2187, hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h2470, hlam, p2662_0]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [h1, h2187, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2662_1]
                        · have p2662_0 := h2662c.1
                          have p2662_1 := h2662c.2.1
                          have p2662_2 := h2662c.2.2.1
                          have p2662_3 := h2662c.2.2.2
                          linarith only [hlam, p2662_0]
              · linarith only [h2653, hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              rcases p2644_3 (m.d 0 2) (by simp) with h2748 | h2748
              · rcases p2644_3 (m.d 1 2) (by simp) with h2749 | h2749
                · linarith only [h0, h2749, hlam]
                · rcases p2644_3 (m.d 2 3) (by simp) with h2751 | h2751
                  · linarith only [h2751, h3, hlam]
                  · linarith only [h2469, h2751, hlam]
              · linarith only [h2748, hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              rcases p2644_3 (m.d 0 2) (by simp) with h2755 | h2755
              · rcases p2644_3 (m.d 1 2) (by simp) with h2756 | h2756
                · linarith only [h0, h2756, hlam]
                · rcases p2644_3 (m.d 2 3) (by simp) with h2758 | h2758
                  · linarith only [h2758, h3, hlam]
                  · linarith only [h2470, h2758, hlam]
              · linarith only [h2755, hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [h0, hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [h9, hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [h2031, h5, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p2644_1]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [h2031, hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [h3, hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              rcases p2644_3 (m.d 0 2) (by simp) with h2768 | h2768
              · rcases p2644_3 (m.d 1 2) (by simp) with h2769 | h2769
                · linarith only [h2769, hlam, p2644_0]
                · rcases p2644_3 (m.d 2 3) (by simp) with h2771 | h2771
                  · rcases p2644_3 (m.d 2 4) (by simp) with h2772 | h2772
                    · linarith only [h2469, h2772, hlam]
                    · rcases p2644_3 (m.d 2 5) (by simp) with h2774 | h2774
                      · linarith only [h2470, h2774, hlam]
                      · linarith only [h2031, h2774, hlam]
                  · linarith only [h2771, hlam, p2644_0]
              · linarith only [h0, h2768, hlam]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              rcases p2644_3 (m.d 0 2) (by simp) with h2780 | h2780
              · rcases p2644_3 (m.d 1 2) (by simp) with h2781 | h2781
                · linarith only [h2781, h9, hlam]
                · rcases p2644_3 (m.d 2 3) (by simp) with h2783 | h2783
                  · rcases p2644_3 (m.d 2 4) (by simp) with h2784 | h2784
                    · linarith only [h2469, h2784, hlam]
                    · rcases p2644_3 (m.d 2 5) (by simp) with h2786 | h2786
                      · linarith only [h2470, h2786, hlam]
                      · linarith only [h2471, h2786, hlam]
                  · linarith only [h2469, h2783, hlam]
              · linarith only [h2780, h4, hlam]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [h0, h2031, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2644_1]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [h4, hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [h0, h2471, h3, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2644_1]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [h2469, hlam, p2644_1]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [h2471, hlam, p2644_1]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [h5, hlam, p2644_0]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              rcases p2644_3 (m.d 0 2) (by simp) with h2798 | h2798
              · rcases p2644_3 (m.d 1 2) (by simp) with h2799 | h2799
                · linarith only [h2799, hlam, p2644_0]
                · rcases p2644_3 (m.d 2 3) (by simp) with h2801 | h2801
                  · rcases p2644_3 (m.d 2 4) (by simp) with h2802 | h2802
                    · linarith only [h2471, h2802, hlam]
                    · rcases p2644_3 (m.d 2 5) (by simp) with h2804 | h2804
                      · rcases h3bigk with h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c | h2805c
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          rcases p2805_3 (m.d 0 3) (by simp) with h2807 | h2807
                          · rcases p2805_3 (m.d 1 3) (by simp) with h2808 | h2808
                            · linarith only [h1, h2808, hlam]
                            · rcases p2805_3 (m.d 2 3) (by simp) with h2810 | h2810
                              · linarith only [h2810, h3, hlam]
                              · linarith only [h2810, h9, hlam]
                          · linarith only [h1, h2807, hlam]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h0, h2470, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2644_1, p2805_1]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h2469, h2471, h2802, h6, h8, hlam, p2644_1, p2805_2]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          rcases p2805_3 (m.d 0 3) (by simp) with h2816 | h2816
                          · rcases p2805_3 (m.d 1 3) (by simp) with h2817 | h2817
                            · linarith only [h1, h2817, hlam]
                            · linarith only [h2187, h2817, hlam]
                          · linarith only [h2816, hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h1, hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h9, hlam, p2805_1]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          rcases p2805_3 (m.d 0 3) (by simp) with h2824 | h2824
                          · rcases p2805_3 (m.d 1 3) (by simp) with h2825 | h2825
                            · rcases p2805_3 (m.d 2 3) (by simp) with h2826 | h2826
                              · rcases p2805_3 (m.d 3 4) (by simp) with h2827 | h2827
                                · linarith only [h2827, hlam, p2805_0]
                                · rcases p2805_3 (m.d 3 5) (by simp) with h2829 | h2829
                                  · linarith only [h2187, h2829, hlam]
                                  · linarith only [h2642, h2829, hlam]
                              · linarith only [h2469, h2826, hlam]
                            · linarith only [h2825, hlam, p2805_0]
                          · linarith only [h2824, h6, hlam]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          rcases p2805_3 (m.d 0 3) (by simp) with h2835 | h2835
                          · rcases p2805_3 (m.d 1 3) (by simp) with h2836 | h2836
                            · rcases p2805_3 (m.d 2 3) (by simp) with h2837 | h2837
                              · rcases p2805_3 (m.d 3 4) (by simp) with h2838 | h2838
                                · linarith only [h2186, h2838, hlam]
                                · rcases p2805_3 (m.d 3 5) (by simp) with h2840 | h2840
                                  · linarith only [h2840, hlam, p2805_0]
                                  · rcases h5bigk with h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c | h2842c
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [hlam, p2842_0]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      rcases p2842_3 (m.d 0 5) (by simp) with h2844 | h2844
                                      · rcases p2842_3 (m.d 1 5) (by simp) with h2845 | h2845
                                        · linarith only [h2, h2845, hlam]
                                        · rcases p2842_3 (m.d 2 5) (by simp) with h2847 | h2847
                                          · linarith only [h2847, h5, hlam]
                                          · linarith only [h2031, h2847, hlam]
                                      · linarith only [h2, h2844, hlam]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2644_1, p2842_1]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      rcases p2842_3 (m.d 0 5) (by simp) with h2852 | h2852
                                      · rcases p2842_3 (m.d 1 5) (by simp) with h2853 | h2853
                                        · linarith only [h2, h2853, hlam]
                                        · linarith only [h2187, h2853, hlam]
                                      · linarith only [h2852, h7, hlam]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h0, h2188, h3, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2842_1]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h2, hlam, p2842_0]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [hlam, p2842_0]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h2031, hlam, p2842_0]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p2842_1]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h2188, hlam, p2842_1]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h5, hlam, p2842_1]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h0, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p2842_1]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [hlam, p2842_0]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h0, h2470, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p2842_1]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h2471, hlam, p2842_1]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h7, hlam, p2842_0]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h2187, hlam, p2842_0]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h2470, hlam, p2842_0]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [hlam, p2842_0]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h2642, hlam, p2842_1]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h8, hlam, p2842_0]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h2031, hc12, hc45, hlam, hphi, ht23, ht34, p2842_1]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p2842_1]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p2842_1]
                                    · have p2842_0 := h2842c.1
                                      have p2842_1 := h2842c.2.1
                                      have p2842_2 := h2842c.2.2.1
                                      have p2842_3 := h2842c.2.2.2
                                      linarith only [hlam, p2842_0]
                              · linarith only [h2470, h2837, hlam]
                            · linarith only [h2836, hlam, p2805_0]
                          · linarith only [h2835, h7, hlam]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h3, hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h0, h2186, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2805_1]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          rcases p2805_3 (m.d 0 3) (by simp) with h2884 | h2884
                          · rcases p2805_3 (m.d 1 3) (by simp) with h2885 | h2885
                            · linarith only [h2885, h9, hlam]
                            · linarith only [h2186, h2885, hlam]
                          · linarith only [h2884, h6, hlam]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          rcases p2805_3 (m.d 0 3) (by simp) with h2889 | h2889
                          · rcases p2805_3 (m.d 1 3) (by simp) with h2890 | h2890
                            · linarith only [h2890, h9, hlam]
                            · linarith only [h2187, h2890, hlam]
                          · linarith only [h2889, h7, hlam]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h6, hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h2186, hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h2469, hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h2642, hlam, p2805_1]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h7, hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h2187, hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h2470, hlam, p2805_0]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [h1, h2187, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2805_1]
                        · have p2805_0 := h2805c.1
                          have p2805_1 := h2805c.2.1
                          have p2805_2 := h2805c.2.2.1
                          have p2805_3 := h2805c.2.2.2
                          linarith only [hlam, p2805_0]
                      · linarith only [h2804, hlam, p2644_0]
                  · linarith only [h2801, h9, hlam]
              · linarith only [h0, h2798, hlam]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [h2470, hlam, p2644_1]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              rcases p2644_3 (m.d 0 2) (by simp) with h2908 | h2908
              · rcases p2644_3 (m.d 1 2) (by simp) with h2909 | h2909
                · linarith only [h2031, h2909, hlam]
                · rcases p2644_3 (m.d 2 3) (by simp) with h2911 | h2911
                  · rcases p2644_3 (m.d 2 4) (by simp) with h2912 | h2912
                    · linarith only [h2471, h2912, hlam]
                    · rcases p2644_3 (m.d 2 5) (by simp) with h2914 | h2914
                      · rcases h3bigk with h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c | h2915c
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          rcases p2915_3 (m.d 0 3) (by simp) with h2917 | h2917
                          · rcases p2915_3 (m.d 1 3) (by simp) with h2918 | h2918
                            · linarith only [h1, h2918, hlam]
                            · rcases p2915_3 (m.d 2 3) (by simp) with h2920 | h2920
                              · linarith only [h2920, h3, hlam]
                              · linarith only [h2920, h9, hlam]
                          · linarith only [h1, h2917, hlam]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h0, h2470, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2644_1, p2915_1]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h2469, h2471, h6, h8, hlam, p2644_1, p2915_2]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          rcases p2915_3 (m.d 0 3) (by simp) with h2926 | h2926
                          · rcases p2915_3 (m.d 1 3) (by simp) with h2927 | h2927
                            · linarith only [h1, h2927, hlam]
                            · linarith only [h2187, h2927, hlam]
                          · linarith only [h2926, hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h1, hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h9, hlam, p2915_1]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          rcases p2915_3 (m.d 0 3) (by simp) with h2934 | h2934
                          · rcases p2915_3 (m.d 1 3) (by simp) with h2935 | h2935
                            · rcases p2915_3 (m.d 2 3) (by simp) with h2936 | h2936
                              · rcases p2915_3 (m.d 3 4) (by simp) with h2937 | h2937
                                · linarith only [h2937, hlam, p2915_0]
                                · rcases p2915_3 (m.d 3 5) (by simp) with h2939 | h2939
                                  · linarith only [h2187, h2939, hlam]
                                  · linarith only [h2642, h2939, hlam]
                              · linarith only [h2469, h2936, hlam]
                            · linarith only [h2935, hlam, p2915_0]
                          · linarith only [h2934, h6, hlam]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          rcases p2915_3 (m.d 0 3) (by simp) with h2945 | h2945
                          · rcases p2915_3 (m.d 1 3) (by simp) with h2946 | h2946
                            · rcases p2915_3 (m.d 2 3) (by simp) with h2947 | h2947
                              · rcases p2915_3 (m.d 3 4) (by simp) with h2948 | h2948
                                · linarith only [h2186, h2948, hlam]
                                · rcases p2915_3 (m.d 3 5) (by simp) with h2950 | h2950
                                  · linarith only [h2950, hlam, p2915_0]
                                  · rcases h5bigk with h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      rcases p2952_3 (m.d 0 5) (by simp) with h2954 | h2954
                                      · rcases p2952_3 (m.d 1 5) (by simp) with h2955 | h2955
                                        · linarith only [h2, h2955, hlam]
                                        · rcases p2952_3 (m.d 2 5) (by simp) with h2957 | h2957
                                          · linarith only [h2957, h5, hlam]
                                          · linarith only [h2031, h2957, hlam]
                                      · linarith only [h2, h2954, hlam]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2909, h6, h8, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2644_1, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      rcases p2952_3 (m.d 0 5) (by simp) with h2962 | h2962
                                      · rcases p2952_3 (m.d 1 5) (by simp) with h2963 | h2963
                                        · linarith only [h2, h2963, hlam]
                                        · linarith only [h2187, h2963, hlam]
                                      · linarith only [h2962, h7, hlam]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h0, h2471, h2909, h3, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2644_1, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2031, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2188, hlam, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h5, hlam, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h0, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h0, h2471, h3, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2471, hlam, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h7, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2187, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2470, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2642, hlam, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h8, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h0, h2031, h3, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h0, h3, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hlam, p2952_0]
                              · linarith only [h2470, h2947, hlam]
                            · linarith only [h2946, hlam, p2915_0]
                          · linarith only [h2945, h7, hlam]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h3, hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h0, h2186, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2915_1]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          rcases p2915_3 (m.d 0 3) (by simp) with h2994 | h2994
                          · rcases p2915_3 (m.d 1 3) (by simp) with h2995 | h2995
                            · linarith only [h2995, h9, hlam]
                            · linarith only [h2186, h2995, hlam]
                          · linarith only [h2994, h6, hlam]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          rcases p2915_3 (m.d 0 3) (by simp) with h2999 | h2999
                          · rcases p2915_3 (m.d 1 3) (by simp) with h3000 | h3000
                            · linarith only [h3000, h9, hlam]
                            · linarith only [h2187, h3000, hlam]
                          · linarith only [h2999, h7, hlam]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h6, hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h2186, hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h2469, hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h2642, hlam, p2915_1]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h7, hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h2187, hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h2470, hlam, p2915_0]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [h1, h2187, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2915_1]
                        · have p2915_0 := h2915c.1
                          have p2915_1 := h2915c.2.1
                          have p2915_2 := h2915c.2.2.1
                          have p2915_3 := h2915c.2.2.2
                          linarith only [hlam, p2915_0]
                      · linarith only [h2471, h2914, hlam]
                  · linarith only [h2469, h2911, hlam]
              · linarith only [h2908, h4, hlam]
            · have p2644_0 := h2644c.1
              have p2644_1 := h2644c.2.1
              have p2644_2 := h2644c.2.2.1
              have p2644_3 := h2644c.2.2.2
              linarith only [hlam, p2644_0]
      · linarith only [h2187, h2470, h9, hlam]
    · linarith only [h2186, h2469, h9, hlam]

end R2N4
