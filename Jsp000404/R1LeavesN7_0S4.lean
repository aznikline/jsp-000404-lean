import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x9 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 2) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 2) ∧ (m.d 1 5) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 5) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  rcases p1737_3 (m.d 0 1) (by simp) with h2196 | h2196
  · rcases p1737_3 (m.d 1 2) (by simp) with h2197 | h2197
    · rcases p1737_3 (m.d 1 3) (by simp) with h2198 | h2198
      · linarith only [h10, h2198, hlam]
      · rcases p1737_3 (m.d 1 4) (by simp) with h2200 | h2200
        · linarith only [h11, h2200, hlam]
        · rcases p1737_3 (m.d 1 5) (by simp) with h2202 | h2202
          · linarith only [h12, h2202, hlam]
          · rcases h1emax with h2204 | h2204 | h2204 | h2204 | h2204
            · linarith only [h0, h10, h13, h2204, h4, h7, h9, h918, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h11, h2204, h498, h912, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1737_1]
            · rcases h2bigk with h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h0, h11, h498, h912, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p2207_1]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h10, h13, h4, h7, h9, h918, hlam, p2207_2]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                rcases p2207_3 (m.d 0 2) (by simp) with h2211 | h2211
                · rcases p2207_3 (m.d 1 2) (by simp) with h2212 | h2212
                  · linarith only [h0, h2212, hlam]
                  · linarith only [h11, h2212, hlam]
                · linarith only [h2211, hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                rcases p2207_3 (m.d 0 2) (by simp) with h2216 | h2216
                · rcases p2207_3 (m.d 1 2) (by simp) with h2217 | h2217
                  · linarith only [h0, h2217, hlam]
                  · linarith only [h12, h2217, hlam]
                · linarith only [h2216, hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h0, hlam, p2207_1]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                rcases p2207_3 (m.d 0 2) (by simp) with h2223 | h2223
                · rcases p2207_3 (m.d 1 2) (by simp) with h2224 | h2224
                  · rcases p2207_3 (m.d 2 3) (by simp) with h2225 | h2225
                    · linarith only [h2225, hlam, p2207_0]
                    · rcases p2207_3 (m.d 2 4) (by simp) with h2227 | h2227
                      · linarith only [h11, h2227, hlam]
                      · linarith only [h2227, h912, hlam]
                  · linarith only [h2224, hlam, p2207_0]
                · linarith only [h2223, h4, hlam]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                rcases p2207_3 (m.d 0 2) (by simp) with h2232 | h2232
                · rcases p2207_3 (m.d 1 2) (by simp) with h2233 | h2233
                  · rcases p2207_3 (m.d 2 3) (by simp) with h2234 | h2234
                    · linarith only [h10, h2234, hlam]
                    · rcases p2207_3 (m.d 2 4) (by simp) with h2236 | h2236
                      · linarith only [h2236, hlam, p2207_0]
                      · rcases p2207_3 (m.d 2 5) (by simp) with h2238 | h2238
                        · linarith only [h12, h2238, hlam]
                        · linarith only [h2238, h916, hlam]
                  · linarith only [h2233, hlam, p2207_0]
                · linarith only [h2232, h5, hlam]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                rcases p2207_3 (m.d 0 2) (by simp) with h2243 | h2243
                · rcases p2207_3 (m.d 1 2) (by simp) with h2244 | h2244
                  · rcases p2207_3 (m.d 2 3) (by simp) with h2245 | h2245
                    · linarith only [h10, h2245, hlam]
                    · rcases p2207_3 (m.d 2 4) (by simp) with h2247 | h2247
                      · linarith only [h11, h2247, hlam]
                      · rcases p2207_3 (m.d 2 5) (by simp) with h2249 | h2249
                        · linarith only [h2249, hlam, p2207_0]
                        · rcases h4bigk with h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c | h2251c
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            rcases p2251_3 (m.d 0 4) (by simp) with h2253 | h2253
                            · rcases p2251_3 (m.d 1 4) (by simp) with h2254 | h2254
                              · linarith only [h2, h2254, hlam]
                              · rcases p2251_3 (m.d 2 4) (by simp) with h2256 | h2256
                                · linarith only [h2256, h5, hlam]
                                · rcases p2251_3 (m.d 3 4) (by simp) with h2258 | h2258
                                  · linarith only [h2258, h7, hlam]
                                  · linarith only [h13, h2258, hlam]
                            · linarith only [h2, h2253, hlam]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            rcases p2251_3 (m.d 0 4) (by simp) with h2262 | h2262
                            · rcases p2251_3 (m.d 1 4) (by simp) with h2263 | h2263
                              · linarith only [h2, h2263, hlam]
                              · linarith only [h11, h2263, hlam]
                            · linarith only [h2262, h5, hlam]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            rcases p2251_3 (m.d 0 4) (by simp) with h2267 | h2267
                            · rcases p2251_3 (m.d 1 4) (by simp) with h2268 | h2268
                              · linarith only [h2, h2268, hlam]
                              · rcases p2251_3 (m.d 2 4) (by simp) with h2270 | h2270
                                · linarith only [h2270, h5, hlam]
                                · rcases p2251_3 (m.d 3 4) (by simp) with h2272 | h2272
                                  · linarith only [h2272, h7, hlam]
                                  · rcases p2251_3 (m.d 4 5) (by simp) with h2274 | h2274
                                    · linarith only [h2274, h9, hlam]
                                    · linarith only [h2274, h918, hlam]
                            · linarith only [h2267, h7, hlam]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h10, h13, h4, h7, h918, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h2, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h498, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1737_1, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h13, hlam, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h498, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h5, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h11, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h912, hlam, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h916, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h7, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h918, hc14, hc45, hlam, hphi, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h0, h4, h7, h9, h918, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h918, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h9, hlam, p2251_0]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            rcases p2251_3 (m.d 0 4) (by simp) with h2295 | h2295
                            · rcases p2251_3 (m.d 1 4) (by simp) with h2296 | h2296
                              · linarith only [h2296, hlam, p2251_0]
                              · rcases p2251_3 (m.d 2 4) (by simp) with h2298 | h2298
                                · linarith only [h2298, h916, hlam]
                                · rcases p2251_3 (m.d 3 4) (by simp) with h2300 | h2300
                                  · linarith only [h2300, h918, hlam]
                                  · linarith only [h13, h2300, hlam]
                            · linarith only [h2, h2295, hlam]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            rcases p2251_3 (m.d 0 4) (by simp) with h2304 | h2304
                            · rcases p2251_3 (m.d 1 4) (by simp) with h2305 | h2305
                              · linarith only [h2305, h498, hlam]
                              · linarith only [h11, h2305, hlam]
                            · linarith only [h2304, h5, hlam]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [h0, h10, h13, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2251_1]
                          · have p2251_0 := h2251c.1
                            have p2251_1 := h2251c.2.1
                            have p2251_2 := h2251c.2.2.1
                            have p2251_3 := h2251c.2.2.2
                            linarith only [hlam, p2251_0]
                  · linarith only [h2244, hlam, p2207_0]
                · linarith only [h2243, h6, hlam]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h4, hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h10, hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h912, hlam, p2207_1]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h914, hlam, p2207_1]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h5, hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h11, hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2207_1]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h916, hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h6, hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h12, hlam, p2207_0]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p2207_1]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [h0, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p2207_1]
              · have p2207_0 := h2207c.1
                have p2207_1 := h2207c.2.1
                have p2207_2 := h2207c.2.2.1
                have p2207_3 := h2207c.2.2.2
                linarith only [hlam, p2207_0]
            · rcases h2bigk with h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c | h2328c
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h0, h498, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p2328_1]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h10, h13, h4, h7, h9, h918, hlam, p2328_2]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                rcases p2328_3 (m.d 0 2) (by simp) with h2332 | h2332
                · rcases p2328_3 (m.d 1 2) (by simp) with h2333 | h2333
                  · linarith only [h0, h2333, hlam]
                  · linarith only [h11, h2333, hlam]
                · linarith only [h2332, hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                rcases p2328_3 (m.d 0 2) (by simp) with h2337 | h2337
                · rcases p2328_3 (m.d 1 2) (by simp) with h2338 | h2338
                  · linarith only [h0, h2338, hlam]
                  · linarith only [h12, h2338, hlam]
                · linarith only [h2337, hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h0, hlam, p2328_1]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                rcases p2328_3 (m.d 0 2) (by simp) with h2344 | h2344
                · rcases p2328_3 (m.d 1 2) (by simp) with h2345 | h2345
                  · rcases p2328_3 (m.d 2 3) (by simp) with h2346 | h2346
                    · linarith only [h2346, hlam, p2328_0]
                    · rcases p2328_3 (m.d 2 4) (by simp) with h2348 | h2348
                      · linarith only [h11, h2348, hlam]
                      · linarith only [h2348, h912, hlam]
                  · linarith only [h2345, hlam, p2328_0]
                · linarith only [h2344, h4, hlam]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                rcases p2328_3 (m.d 0 2) (by simp) with h2353 | h2353
                · rcases p2328_3 (m.d 1 2) (by simp) with h2354 | h2354
                  · rcases p2328_3 (m.d 2 3) (by simp) with h2355 | h2355
                    · linarith only [h10, h2355, hlam]
                    · rcases p2328_3 (m.d 2 4) (by simp) with h2357 | h2357
                      · linarith only [h2357, hlam, p2328_0]
                      · rcases p2328_3 (m.d 2 5) (by simp) with h2359 | h2359
                        · linarith only [h12, h2359, hlam]
                        · linarith only [h2359, h916, hlam]
                  · linarith only [h2354, hlam, p2328_0]
                · linarith only [h2353, h5, hlam]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                rcases p2328_3 (m.d 0 2) (by simp) with h2364 | h2364
                · rcases p2328_3 (m.d 1 2) (by simp) with h2365 | h2365
                  · rcases p2328_3 (m.d 2 3) (by simp) with h2366 | h2366
                    · linarith only [h10, h2366, hlam]
                    · rcases p2328_3 (m.d 2 4) (by simp) with h2368 | h2368
                      · linarith only [h11, h2368, hlam]
                      · rcases p2328_3 (m.d 2 5) (by simp) with h2370 | h2370
                        · linarith only [h2370, hlam, p2328_0]
                        · rcases h4bigk with h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c | h2372c
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [hlam, p2372_0]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            rcases p2372_3 (m.d 0 4) (by simp) with h2374 | h2374
                            · rcases p2372_3 (m.d 1 4) (by simp) with h2375 | h2375
                              · linarith only [h2, h2375, hlam]
                              · rcases p2372_3 (m.d 2 4) (by simp) with h2377 | h2377
                                · linarith only [h2377, h5, hlam]
                                · rcases p2372_3 (m.d 3 4) (by simp) with h2379 | h2379
                                  · linarith only [h2379, h7, hlam]
                                  · linarith only [h13, h2379, hlam]
                            · linarith only [h2, h2374, hlam]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            rcases p2372_3 (m.d 0 4) (by simp) with h2383 | h2383
                            · rcases p2372_3 (m.d 1 4) (by simp) with h2384 | h2384
                              · linarith only [h2, h2384, hlam]
                              · linarith only [h11, h2384, hlam]
                            · linarith only [h2383, h5, hlam]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            rcases p2372_3 (m.d 0 4) (by simp) with h2388 | h2388
                            · rcases p2372_3 (m.d 1 4) (by simp) with h2389 | h2389
                              · linarith only [h2, h2389, hlam]
                              · rcases p2372_3 (m.d 2 4) (by simp) with h2391 | h2391
                                · linarith only [h2391, h5, hlam]
                                · rcases p2372_3 (m.d 3 4) (by simp) with h2393 | h2393
                                  · linarith only [h2393, h7, hlam]
                                  · rcases p2372_3 (m.d 4 5) (by simp) with h2395 | h2395
                                    · linarith only [h2395, h9, hlam]
                                    · linarith only [h2395, h918, hlam]
                            · linarith only [h2388, h7, hlam]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h13, h4, h7, h918, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2372_1]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h2, hlam, p2372_0]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [hlam, p2372_0]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h0, h498, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p2372_1]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h13, hlam, p2372_1]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h498, hlam, p2372_0]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h5, hlam, p2372_0]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h11, hlam, p2372_0]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [hlam, p2372_0]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h912, hlam, p2372_1]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h916, hlam, p2372_0]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h7, hlam, p2372_0]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h918, hc14, hc45, hlam, hphi, p2372_1]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h0, h4, h7, h9, h918, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2372_1]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [hlam, p2372_0]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h918, hlam, p2372_0]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h9, hlam, p2372_0]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            rcases p2372_3 (m.d 0 4) (by simp) with h2416 | h2416
                            · rcases p2372_3 (m.d 1 4) (by simp) with h2417 | h2417
                              · linarith only [h2417, hlam, p2372_0]
                              · rcases p2372_3 (m.d 2 4) (by simp) with h2419 | h2419
                                · linarith only [h2419, h916, hlam]
                                · rcases p2372_3 (m.d 3 4) (by simp) with h2421 | h2421
                                  · linarith only [h2421, h918, hlam]
                                  · linarith only [h13, h2421, hlam]
                            · linarith only [h2, h2416, hlam]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            rcases p2372_3 (m.d 0 4) (by simp) with h2425 | h2425
                            · rcases p2372_3 (m.d 1 4) (by simp) with h2426 | h2426
                              · linarith only [h2426, h498, hlam]
                              · linarith only [h11, h2426, hlam]
                            · linarith only [h2425, h5, hlam]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [h0, h10, h13, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2372_1]
                          · have p2372_0 := h2372c.1
                            have p2372_1 := h2372c.2.1
                            have p2372_2 := h2372c.2.2.1
                            have p2372_3 := h2372c.2.2.2
                            linarith only [hlam, p2372_0]
                  · linarith only [h2365, hlam, p2328_0]
                · linarith only [h2364, h6, hlam]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h4, hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h10, hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h912, hlam, p2328_1]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h914, hlam, p2328_1]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h5, hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h11, hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2328_1]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h916, hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h6, hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h12, hlam, p2328_0]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p2328_1]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [h0, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p2328_1]
              · have p2328_0 := h2328c.1
                have p2328_1 := h2328c.2.1
                have p2328_2 := h2328c.2.2.1
                have p2328_3 := h2328c.2.2.2
                linarith only [hlam, p2328_0]
            · rcases h2bigk with h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c | h2449c
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p1737_1, p2449_1]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h10, h13, h4, h7, h9, h918, hlam, p2449_2]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                rcases p2449_3 (m.d 0 2) (by simp) with h2453 | h2453
                · rcases p2449_3 (m.d 1 2) (by simp) with h2454 | h2454
                  · linarith only [h0, h2454, hlam]
                  · linarith only [h11, h2454, hlam]
                · linarith only [h2453, hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                rcases p2449_3 (m.d 0 2) (by simp) with h2458 | h2458
                · rcases p2449_3 (m.d 1 2) (by simp) with h2459 | h2459
                  · linarith only [h0, h2459, hlam]
                  · linarith only [h12, h2459, hlam]
                · linarith only [h2458, hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h0, hlam, p2449_1]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                rcases p2449_3 (m.d 0 2) (by simp) with h2465 | h2465
                · rcases p2449_3 (m.d 1 2) (by simp) with h2466 | h2466
                  · rcases p2449_3 (m.d 2 3) (by simp) with h2467 | h2467
                    · linarith only [h2467, hlam, p2449_0]
                    · rcases p2449_3 (m.d 2 4) (by simp) with h2469 | h2469
                      · linarith only [h11, h2469, hlam]
                      · linarith only [h2469, h912, hlam]
                  · linarith only [h2466, hlam, p2449_0]
                · linarith only [h2465, h4, hlam]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                rcases p2449_3 (m.d 0 2) (by simp) with h2474 | h2474
                · rcases p2449_3 (m.d 1 2) (by simp) with h2475 | h2475
                  · rcases p2449_3 (m.d 2 3) (by simp) with h2476 | h2476
                    · linarith only [h10, h2476, hlam]
                    · rcases p2449_3 (m.d 2 4) (by simp) with h2478 | h2478
                      · linarith only [h2478, hlam, p2449_0]
                      · rcases p2449_3 (m.d 2 5) (by simp) with h2480 | h2480
                        · linarith only [h12, h2480, hlam]
                        · linarith only [h2480, h916, hlam]
                  · linarith only [h2475, hlam, p2449_0]
                · linarith only [h2474, h5, hlam]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                rcases p2449_3 (m.d 0 2) (by simp) with h2485 | h2485
                · rcases p2449_3 (m.d 1 2) (by simp) with h2486 | h2486
                  · rcases p2449_3 (m.d 2 3) (by simp) with h2487 | h2487
                    · linarith only [h10, h2487, hlam]
                    · rcases p2449_3 (m.d 2 4) (by simp) with h2489 | h2489
                      · linarith only [h11, h2489, hlam]
                      · rcases p2449_3 (m.d 2 5) (by simp) with h2491 | h2491
                        · linarith only [h2491, hlam, p2449_0]
                        · rcases h4bigk with h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [hlam, p2493_0]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            rcases p2493_3 (m.d 0 4) (by simp) with h2495 | h2495
                            · rcases p2493_3 (m.d 1 4) (by simp) with h2496 | h2496
                              · linarith only [h2, h2496, hlam]
                              · rcases p2493_3 (m.d 2 4) (by simp) with h2498 | h2498
                                · linarith only [h2498, h5, hlam]
                                · rcases p2493_3 (m.d 3 4) (by simp) with h2500 | h2500
                                  · linarith only [h2500, h7, hlam]
                                  · linarith only [h13, h2500, hlam]
                            · linarith only [h2, h2495, hlam]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            rcases p2493_3 (m.d 0 4) (by simp) with h2504 | h2504
                            · rcases p2493_3 (m.d 1 4) (by simp) with h2505 | h2505
                              · linarith only [h2, h2505, hlam]
                              · linarith only [h11, h2505, hlam]
                            · linarith only [h2504, h5, hlam]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            rcases p2493_3 (m.d 0 4) (by simp) with h2509 | h2509
                            · rcases p2493_3 (m.d 1 4) (by simp) with h2510 | h2510
                              · linarith only [h2, h2510, hlam]
                              · rcases p2493_3 (m.d 2 4) (by simp) with h2512 | h2512
                                · linarith only [h2512, h5, hlam]
                                · rcases p2493_3 (m.d 3 4) (by simp) with h2514 | h2514
                                  · linarith only [h2514, h7, hlam]
                                  · rcases p2493_3 (m.d 4 5) (by simp) with h2516 | h2516
                                    · linarith only [h2516, h9, hlam]
                                    · linarith only [h2516, h918, hlam]
                            · linarith only [h2509, h7, hlam]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h13, h4, h7, h918, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2493_1]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h2, hlam, p2493_0]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [hlam, p2493_0]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h0, h498, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p2493_1]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h13, hlam, p2493_1]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h498, hlam, p2493_0]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h5, hlam, p2493_0]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h11, hlam, p2493_0]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [hlam, p2493_0]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h912, hlam, p2493_1]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h916, hlam, p2493_0]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h7, hlam, p2493_0]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h918, hc14, hc45, hlam, hphi, p2493_1]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h0, h4, h7, h9, h918, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2493_1]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [hlam, p2493_0]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h918, hlam, p2493_0]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h9, hlam, p2493_0]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            rcases p2493_3 (m.d 0 4) (by simp) with h2537 | h2537
                            · rcases p2493_3 (m.d 1 4) (by simp) with h2538 | h2538
                              · linarith only [h2538, hlam, p2493_0]
                              · rcases p2493_3 (m.d 2 4) (by simp) with h2540 | h2540
                                · linarith only [h2540, h916, hlam]
                                · rcases p2493_3 (m.d 3 4) (by simp) with h2542 | h2542
                                  · linarith only [h2542, h918, hlam]
                                  · linarith only [h13, h2542, hlam]
                            · linarith only [h2, h2537, hlam]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            rcases p2493_3 (m.d 0 4) (by simp) with h2546 | h2546
                            · rcases p2493_3 (m.d 1 4) (by simp) with h2547 | h2547
                              · linarith only [h2547, h498, hlam]
                              · linarith only [h11, h2547, hlam]
                            · linarith only [h2546, h5, hlam]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [h0, h10, h13, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2493_1]
                          · have p2493_0 := h2493c.1
                            have p2493_1 := h2493c.2.1
                            have p2493_2 := h2493c.2.2.1
                            have p2493_3 := h2493c.2.2.2
                            linarith only [hlam, p2493_0]
                  · linarith only [h2486, hlam, p2449_0]
                · linarith only [h2485, h6, hlam]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h4, hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h10, hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h912, hlam, p2449_1]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h914, hlam, p2449_1]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h5, hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h11, hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2449_1]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h916, hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h6, hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h12, hlam, p2449_0]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1, p2449_1]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [h0, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1737_1, p2449_1]
              · have p2449_0 := h2449c.1
                have p2449_1 := h2449c.2.1
                have p2449_2 := h2449c.2.2.1
                have p2449_3 := h2449c.2.2.2
                linarith only [hlam, p2449_0]
    · linarith only [h12, h2197, hlam]
  · linarith only [h2196, h3, hlam]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x10 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 3) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 3) ∧ (m.d 0 1) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 0 1) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [h1, hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x11 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 3) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 3) ∧ (m.d 1 2) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 2) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [h10, hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x12 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 3) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 3) ∧ (m.d 1 3) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 3) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x13 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 3) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 3) ∧ (m.d 1 4) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 4) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [h13, hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x14 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 3) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 3) ∧ (m.d 1 5) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 5) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [h437, hlam, p1737_1]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x15 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 4) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 4) ∧ (m.d 0 1) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 0 1) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [h2, hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x16 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 4) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 4) ∧ (m.d 1 2) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 2) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [h11, hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x17 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 4) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 4) ∧ (m.d 1 3) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 3) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [h0, h10, h4, h498, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1737_1]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x18 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 4) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 4) ∧ (m.d 1 4) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 4) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x19 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 4) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 4) ∧ (m.d 1 5) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 5) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [h498, hlam, p1737_1]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x20 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 5) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 5) ∧ (m.d 0 1) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 0 1) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [h3, hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x21 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 5) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 5) ∧ (m.d 1 2) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 2) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  linarith only [h12, hlam, p1737_0]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x1_x1_x22 (m : N7Model)
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
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h918 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h1737c : ((m.d 1 5) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 5) ∧ (m.d 1 3) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 3) ≤ z)))
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
  have h11 := hg11
  have h12 := hg12
  have p1737_0 := h1737c.1
  have p1737_1 := h1737c.2.1
  have p1737_2 := h1737c.2.2.1
  have p1737_3 := h1737c.2.2.2
  rcases p1737_3 (m.d 0 1) (by simp) with h2584 | h2584
  · rcases p1737_3 (m.d 1 2) (by simp) with h2585 | h2585
    · rcases p1737_3 (m.d 1 3) (by simp) with h2586 | h2586
      · linarith only [h2586, h437, hlam]
      · rcases p1737_3 (m.d 1 4) (by simp) with h2588 | h2588
        · linarith only [h2588, h498, hlam]
        · linarith only [h13, h2588, hlam]
    · linarith only [h10, h2585, hlam]
  · linarith only [h1, h2584, hlam]

end R2N4
