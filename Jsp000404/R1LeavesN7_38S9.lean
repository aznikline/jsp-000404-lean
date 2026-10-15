import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1917 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2259 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2260 | h2260
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2261 | h2261
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2262 | h2262
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2263 | h2263
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2264 | h2264
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2265 | h2265
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2266 | h2266
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2267 | h2267
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2268 | h2268
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2269 | h2269
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2270 | h2270
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2271 | h2271
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2272 | h2272
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2273 | h2273
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2274 | h2274
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2275 | h2275
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2276 | h2276
                                  · rcases h0bigk with h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [hlam, p2277_0]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h0, hlam, p2277_1]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h1917, hlam, p2277_0]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h2259, h2268, h2273, h2276, hc01, hc45, hlam, hphi, ht0b, ht5b, p2277_1]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h1917, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p2277_1]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p2277_1]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [hlam, p2277_0]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h0, h1917, h2259, h2268, h2273, h2276, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2277_1]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h0, h2259, h2268, h2273, h2276, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2277_1]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      rcases p2277_3 (m.d 0 1) (by simp) with h2287 | h2287
                                      · linarith only [h0, h2287, hlam]
                                      · linarith only [h2260, h2287, hlam]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h2259, h2268, h2273, h2276, hc03, hc45, hlam, hphi, ht0b, ht5b, p2277_1]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h2261, hlam, p2277_1]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [hlam, p2277_0]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h1917, h2259, h2267, h2268, h2273, h2276, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2277_1]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      rcases p2277_3 (m.d 0 1) (by simp) with h2294 | h2294
                                      · linarith only [h1917, h2294, hlam]
                                      · linarith only [h2260, h2294, hlam]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h2259, hlam, p2277_0]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h2262, hlam, p2277_0]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h2264, hlam, p2277_0]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [hlam, p2277_0]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h2260, h2269, h2274, h2276, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2277_1, u4elo0]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h2260, hlam, p2277_0]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h2263, hlam, p2277_1]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h2265, hlam, p2277_0]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [h2266, hlam, p2277_1]
                                    · have p2277_0 := h2277c.1
                                      have p2277_1 := h2277c.2.1
                                      have p2277_2 := h2277c.2.2.1
                                      have p2277_3 := h2277c.2.2.2
                                      linarith only [hlam, p2277_0]
                                  · linarith only [h2266, h2276, hc34, hlam, hphi, u4elo0]
                                · linarith only [h2272, h2275, hc24, hlam, hphi, u4elo1]
                              · linarith only [h2265, h2266, h2273, h2274, hc34, hlam, hphi, u4elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2310 | h2310
                              · linarith only [h1917, h2259, h2267, h2270, h2273, h2310, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2312 | h2312
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2313 | h2313
                                  · rcases h0bigk with h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [hlam, p2314_0]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h0, hlam, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h1917, hlam, p2314_0]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h1917, h2267, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h1917, h2267, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [hlam, p2314_0]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h0, h1917, h2259, h2271, h2272, h2310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h0, h2259, h2271, h2272, h2310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h0, h2260, h2271, h2310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h2259, h2271, h2272, h2310, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h2261, hlam, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [hlam, p2314_0]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h0, h2259, h2261, h2271, h2272, h2310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h0, h2260, h2261, h2271, h2310, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h2259, hlam, p2314_0]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h2262, hlam, p2314_0]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h2264, hlam, p2314_0]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [hlam, p2314_0]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h2260, h2271, h2310, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h2260, hlam, p2314_0]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h2263, hlam, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h2265, hlam, p2314_0]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [h2266, hlam, p2314_1]
                                    · have p2314_0 := h2314c.1
                                      have p2314_1 := h2314c.2.1
                                      have p2314_2 := h2314c.2.2.1
                                      have p2314_3 := h2314c.2.2.2
                                      linarith only [hlam, p2314_0]
                                  · linarith only [h2312, h2313, hc34, hlam, hphi, u4elo2]
                                · linarith only [h2272, h2312, hc24, hlam, hphi, u4elo1]
                          · linarith only [h2266, h2272, hc14, hlam, hphi, u4elo0]
                        · linarith only [h1917, h2265, h2271, hlam]
                      · linarith only [h1917, h2270, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2263, h2269, hlam]
                  · linarith only [h0, h2268, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2261, h2267, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2348 | h2348
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2349 | h2349
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2350 | h2350
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2351 | h2351
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2352 | h2352
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2353 | h2353
                          · linarith only [h1917, h2259, h2266, h2348, h2353, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2355 | h2355
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2356 | h2356
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2357 | h2357
                                · linarith only [h2259, h2266, h2349, h2357, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2359 | h2359
                                  · linarith only [h2259, h2266, h2349, h2355, h2359, hlam]
                                  · rcases h0bigk with h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c | h2361c
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [hlam, p2361_0]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h0, hlam, p2361_1]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h1917, hlam, p2361_0]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h1917, h2348, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2361_1]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h1917, h2348, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2361_1]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p2361_1]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [hlam, p2361_0]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h0, h1917, h2260, h2350, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2361_1]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      rcases p2361_3 (m.d 0 1) (by simp) with h2370 | h2370
                                      · linarith only [h0, h2370, hlam]
                                      · linarith only [h2259, h2370, hlam]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      rcases p2361_3 (m.d 0 1) (by simp) with h2373 | h2373
                                      · linarith only [h0, h2373, hlam]
                                      · linarith only [h2260, h2373, hlam]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h2260, h2349, h2353, h2355, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2361_1]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h2261, hlam, p2361_1]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [hlam, p2361_0]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      rcases p2361_3 (m.d 0 1) (by simp) with h2379 | h2379
                                      · linarith only [h1917, h2379, hlam]
                                      · linarith only [h2259, h2379, hlam]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      rcases p2361_3 (m.d 0 1) (by simp) with h2382 | h2382
                                      · linarith only [h1917, h2382, hlam]
                                      · linarith only [h2260, h2382, hlam]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h2259, hlam, p2361_0]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h2262, hlam, p2361_0]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h2264, hlam, p2361_0]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [hlam, p2361_0]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h2266, hlam, p2361_0]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h2260, hlam, p2361_0]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h2263, hlam, p2361_1]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h2265, hlam, p2361_0]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [h0, h2259, h2260, h2349, h2355, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2361_1]
                                    · have p2361_0 := h2361c.1
                                      have p2361_1 := h2361c.2.1
                                      have p2361_2 := h2361c.2.2.1
                                      have p2361_3 := h2361c.2.2.2
                                      linarith only [hlam, p2361_0]
                              · linarith only [h1917, h2260, h2348, h2352, h2355, h2356, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h2264, h2266, h2355, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h1917, h2265, h2352, hlam]
                      · linarith only [h1917, h2351, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2263, h2350, hlam]
                  · linarith only [h1917, h2348, h2349, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2261, h2348, hlam]
            · linarith only [h1917, h2260, h2265, hlam]
          · linarith only [h1917, h2259, h2264, hc14, hlam, hphi, u4elo3]
        · linarith only [h0, h2260, h2263, hlam]
      · linarith only [h1917, h2259, h2261, h2262, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2406 | h2406
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2407 | h2407
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2408 | h2408
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2409 | h2409
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2410 | h2410
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2411 | h2411
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2412 | h2412
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2413 | h2413
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2414 | h2414
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2415 | h2415
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2416 | h2416
                          · linarith only [h0, h2259, h2261, h2411, h2416, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h2410, h2416, hc14, hlam, hphi, u4elo0]
                        · linarith only [h0, h2259, h2261, h2409, h2411, h2414, h2415, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h1917, h2259, h2412, h2414, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h2259, h2261, h2411, h2412, h2413, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h2261, h2411, h2412, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2423 | h2423
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2424 | h2424
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2425 | h2425
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2426 | h2426
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2427 | h2427
                          · linarith only [h0, h2259, h2411, h2427, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h2259, h2410, h2411, h2427, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h1917, h2409, h2426, hlam]
                      · linarith only [h1917, h2425, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2260, h2407, h2424, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h2259, h2410, h2423, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2434 | h2434
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2435 | h2435
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2436 | h2436
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2437 | h2437
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2438 | h2438
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2439 | h2439
                          · linarith only [h0, h2259, h2261, h2410, h2434, h2439, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2441 | h2441
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2442 | h2442
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2443 | h2443
                                · linarith only [h0, h2259, h2261, h2410, h2434, h2435, h2443, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2445 | h2445
                                  · linarith only [h2259, h2410, h2435, h2441, h2445, hlam]
                                  · rcases h0bigk with h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h0, hlam, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h1917, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h0, h2259, h2261, h2434, h2435, h2441, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h0, h2261, h2434, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2261, h2434, hc01, hc12, hlam, hphi, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2261, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2259, h2261, h2434, h2435, h2441, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2260, h2261, h2434, h2436, h2442, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2259, h2435, h2441, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2261, h2434, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2259, h2261, h2434, h2435, h2441, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2260, h2261, h2434, h2436, h2442, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2259, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2406, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2408, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2410, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2260, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2407, hlam, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h2409, hlam, p2447_0]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [h0, h2259, h2260, h2435, h2441, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2447_1]
                                    · have p2447_0 := h2447c.1
                                      have p2447_1 := h2447c.2.1
                                      have p2447_2 := h2447c.2.2.1
                                      have p2447_3 := h2447c.2.2.2
                                      linarith only [hlam, p2447_0]
                              · linarith only [h2261, h2409, h2442, hlam]
                            · linarith only [h0, h2261, h2441, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                        · linarith only [h0, h2260, h2261, h2409, h2434, h2438, hlam]
                      · linarith only [h0, h2259, h2261, h2434, h2435, h2437, hc24, hlam, hphi, u4elo3]
                    · linarith only [h2261, h2407, h2436, hc12, hc23, hlam, hphi]
                  · linarith only [h2261, h2434, h2435, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2479 | h2479
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2480 | h2480
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2481 | h2481
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2482 | h2482
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2483 | h2483
                          · linarith only [h2410, h2483, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2485 | h2485
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2486 | h2486
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2487 | h2487
                                · linarith only [h2259, h2410, h2479, h2487, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2489 | h2489
                                  · linarith only [h2259, h2410, h2479, h2485, h2489, hlam]
                                  · rcases h0bigk with h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [hlam, p2491_0]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h0, hlam, p2491_1]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h1917, hlam, p2491_0]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h0, h2434, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2491_1]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h0, h2434, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2491_1]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h2260, hc02, hc15, hlam, hphi, ht0b, ht5b, p2491_1]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [hlam, p2491_0]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h2261, hlam, p2491_0]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h0, h2259, h2434, h2479, h2485, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2491_1]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h0, h2260, h2434, h2480, h2486, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2491_1]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h2259, h2479, h2485, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2491_1]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h1917, h2434, hc02, hc23, hlam, hphi, p2491_1]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [hlam, p2491_0]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      rcases p2491_3 (m.d 0 1) (by simp) with h2505 | h2505
                                      · linarith only [h1917, h2505, hlam]
                                      · linarith only [h2259, h2505, hlam]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      rcases p2491_3 (m.d 0 1) (by simp) with h2508 | h2508
                                      · linarith only [h1917, h2508, hlam]
                                      · linarith only [h2260, h2508, hlam]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h2259, hlam, p2491_0]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h2406, hlam, p2491_0]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h2408, hlam, p2491_0]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [hlam, p2491_0]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h2410, hlam, p2491_0]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h2260, hlam, p2491_0]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h2407, hlam, p2491_1]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h2409, hlam, p2491_0]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [h0, h2259, h2260, h2434, h2479, h2485, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2491_1]
                                    · have p2491_0 := h2491c.1
                                      have p2491_1 := h2491c.2.1
                                      have p2491_2 := h2491c.2.2.1
                                      have p2491_3 := h2491c.2.2.2
                                      linarith only [hlam, p2491_0]
                              · linarith only [h0, h2434, h2486, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h2260, h2434, h2479, h2483, h2485, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h1917, h2409, h2482, hlam]
                      · linarith only [h1917, h2481, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h2260, h2407, h2480, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h2259, h2479, hc14, hlam, hphi, u4elo2]
            · linarith only [h1917, h2260, h2409, hlam]
          · linarith only [h0, h2259, h2261, h2408, hc14, hlam, hphi, u4elo3]
        · linarith only [h0, h2260, h2407, hlam]
      · linarith only [h0, h2259, h2406, hc14, hlam, hphi, u4elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2531 | h2531
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2532 | h2532
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2533 | h2533
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2534 | h2534
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2535 | h2535
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2536 | h2536
              · linarith only [h2259, h2260, h2536, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2538 | h2538
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2539 | h2539
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2540 | h2540
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2541 | h2541
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2542 | h2542
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2543 | h2543
                          · linarith only [h2259, h2260, h2536, h2538, h2542, h2543, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h2259, h2260, h2543, hc14, hlam, hphi, u4elo4]
                        · linarith only [h1917, h2259, h2531, h2535, h2539, h2542, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h1917, h2259, h2539, h2541, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h2533, h2540, hlam]
                  · linarith only [h0, h2531, h2539, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h0, h2259, h2531, h2538, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2551 | h2551
              · linarith only [h1917, h2259, h2535, h2551, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2553 | h2553
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2554 | h2554
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2555 | h2555
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2556 | h2556
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2557 | h2557
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2558 | h2558
                          · linarith only [h1917, h2259, h2535, h2551, h2557, h2558, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h2259, h2260, h2558, hc14, hlam, hphi, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2561 | h2561
                          · linarith only [h1917, h2259, h2557, h2561, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1917, h2259, h2557, h2561, hc14, hlam, hphi, u4elo4]
                      · linarith only [h1917, h2259, h2554, h2556, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h2533, h2555, hlam]
                  · linarith only [h0, h2259, h2554, hc14, hlam, hphi, u4elo2]
                · linarith only [h0, h2531, h2553, hlam]
          · linarith only [h1917, h2259, h2534, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2569 | h2569
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2570 | h2570
            · linarith only [h2531, h2533, h2570, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2572 | h2572
              · linarith only [h1917, h2259, h2531, h2533, h2572, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2574 | h2574
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2575 | h2575
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2576 | h2576
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2577 | h2577
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2578 | h2578
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2579 | h2579
                          · linarith only [h1917, h2259, h2531, h2533, h2572, h2576, h2579, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h2259, h2260, h2579, hc14, hlam, hphi, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2582 | h2582
                          · linarith only [h1917, h2259, h2578, h2582, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h2259, h2533, h2575, h2576, h2582, hc24, hlam, hphi, u4elo4]
                      · linarith only [h1917, h2259, h2575, h2577, hc24, hlam, hphi, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2586 | h2586
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2587 | h2587
                        · linarith only [h1917, h2259, h2570, h2574, h2575, h2576, h2587, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2589 | h2589
                          · linarith only [h0, h2259, h2576, h2589, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h1917, h2259, h2574, h2576, h2589, hc14, hlam, hphi, u4elo4]
                      · linarith only [h1917, h2259, h2575, h2586, hc24, hlam, hphi, u4elo3]
                  · linarith only [h1917, h2574, h2575, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h2259, h2531, h2574, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h1917, h2259, h2569, hc14, hlam, hphi, u4elo3]
      · linarith only [h0, h2259, h2532, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2597 | h2597
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2598 | h2598
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2599 | h2599
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2600 | h2600
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2601 | h2601
              · linarith only [h2259, h2260, h2601, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2603 | h2603
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2604 | h2604
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2605 | h2605
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2606 | h2606
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2607 | h2607
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2608 | h2608
                          · linarith only [h2259, h2260, h2531, h2598, h2601, h2603, h2608, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h2259, h2260, h2606, h2608, hc34, hlam, hphi, u4elo4]
                        · linarith only [h1917, h2259, h2600, h2607, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h1917, h2259, h2604, h2606, hc24, hlam, hphi, u4elo3]
                    · linarith only [h2531, h2598, h2603, h2605, hlam]
                  · linarith only [h2259, h2260, h2531, h2598, h2603, h2604, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2615 | h2615
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2616 | h2616
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2617 | h2617
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2618 | h2618
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2619 | h2619
                          · linarith only [h2259, h2260, h2601, h2616, h2619, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h2259, h2260, h2619, hc14, hlam, hphi, u4elo4]
                        · linarith only [h1917, h2259, h2600, h2615, h2618, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h1917, h2259, h2615, h2617, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h2259, h2598, h2615, h2616, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h2259, h2615, hc14, hlam, hphi, u4elo2]
            · linarith only [h2531, h2598, h2600, hlam]
          · linarith only [h0, h2259, h2531, h2599, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2628 | h2628
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2629 | h2629
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2630 | h2630
              · linarith only [h0, h2259, h2598, h2630, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2632 | h2632
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2633 | h2633
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2634 | h2634
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2635 | h2635
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2636 | h2636
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2637 | h2637
                          · linarith only [h0, h2259, h2598, h2630, h2634, h2637, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h2259, h2598, h2634, h2637, hc14, hlam, hphi, u4elo4]
                        · linarith only [h1917, h2259, h2629, h2636, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h2259, h2531, h2632, h2633, h2635, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h2259, h2531, h2632, h2633, h2634, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h2531, h2632, h2633, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2644 | h2644
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2645 | h2645
                    · linarith only [h0, h2259, h2598, h2632, h2644, h2645, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2647 | h2647
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2648 | h2648
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2649 | h2649
                          · linarith only [h2630, h2649, hc04, hlam, hphi, u4elo1]
                          · linarith only [h0, h2259, h2645, h2647, h2649, hc34, hlam, hphi, u4elo4]
                        · linarith only [h1917, h2629, h2648, hlam]
                      · linarith only [h1917, h2647, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h2259, h2644, hc14, hlam, hphi, u4elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2655 | h2655
              · linarith only [h1917, h2259, h2629, h2655, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2657 | h2657
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2658 | h2658
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2659 | h2659
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2660 | h2660
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2661 | h2661
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2662 | h2662
                          · linarith only [h0, h2259, h2531, h2629, h2655, h2661, h2662, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h2259, h2260, h2658, h2662, hc24, hlam, hphi, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2665 | h2665
                          · linarith only [h1917, h2259, h2661, h2665, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h2259, h2531, h2657, h2661, h2665, hc14, hlam, hphi, u4elo4]
                      · linarith only [h0, h2259, h2531, h2657, h2658, h2660, hc24, hlam, hphi, u4elo3]
                    · linarith only [h0, h2259, h2531, h2657, h2658, h2659, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h2259, h2531, h2657, h2658, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2671 | h2671
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2672 | h2672
                    · linarith only [h0, h2259, h2598, h2657, h2671, h2672, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2674 | h2674
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2675 | h2675
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2676 | h2676
                          · linarith only [h0, h2259, h2657, h2676, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h2259, h2671, h2672, h2676, hc24, hlam, hphi, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2679 | h2679
                          · linarith only [h0, h2259, h2672, h2679, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h2259, h2657, h2671, h2675, h2679, hc24, hlam, hphi, u4elo4]
                      · linarith only [h0, h2259, h2657, h2671, h2674, hc24, hlam, hphi, u4elo3]
                  · linarith only [h0, h2259, h2671, hc14, hlam, hphi, u4elo2]
          · linarith only [h0, h2259, h2531, h2628, hc14, hlam, hphi, u4elo3]
      · linarith only [h0, h2259, h2597, hc14, hlam, hphi, u4elo2]

end R2N4
