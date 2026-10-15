import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_33S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2209 | h2209
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2210 | h2210
    · linarith only [h0, h1, h2210, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2212 | h2212
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2213 | h2213
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2214 | h2214
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2215 | h2215
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2216 | h2216
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2217 | h2217
                · linarith only [h2210, h2217, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1, h2217, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2220 | h2220
                · linarith only [h0, h1, h2210, h2220, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h2220, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h2213, h2215, hlam]
          · linarith only [h0, h1, h2212, h2214, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2225 | h2225
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2226 | h2226
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2227 | h2227
              · linarith only [h2212, h2213, h2227, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2229 | h2229
                · linarith only [h0, h1, h2210, h2229, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h2229, hc12, hlam, hphi, u2elo2]
            · linarith only [h1, h2209, h2226, hlam]
          · linarith only [h0, h1, h2212, h2225, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2234 | h2234
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2235 | h2235
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2236 | h2236
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2237 | h2237
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2238 | h2238
                · linarith only [h0, h1, h2210, h2238, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h2238, hc12, hlam, hphi, u2elo2]
              · linarith only [h2212, h2234, h2237, hlam]
            · linarith only [h0, h1, h2234, h2236, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2243 | h2243
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2244 | h2244
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2245 | h2245
                · linarith only [h0, h1, h2235, h2245, hc23, hc34, hlam, hphi]
                · linarith only [h0, h1, h2245, hc12, hlam, hphi, u2elo2]
              · linarith only [h0, h1, h2210, h2234, h2235, h2244, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h2210, h2234, h2243, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2250 | h2250
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2251 | h2251
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2252 | h2252
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2253 | h2253
                · linarith only [h2210, h2253, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1, h2253, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2256 | h2256
                · linarith only [h0, h2210, h2256, hlam]
                · linarith only [h0, h1, h2256, hc12, hlam, hphi, u2elo2]
            · linarith only [h1, h2209, h2251, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2260 | h2260
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2261 | h2261
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2262 | h2262
                · linarith only [h0, h1, h2250, h2262, hc23, hc34, hlam, hphi]
                · linarith only [h0, h1, h2262, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h2209, h2250, h2261, hlam]
            · linarith only [h1, h2209, h2260, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2267 | h2267
    · linarith only [h0, h1, h2267, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2269 | h2269
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2270 | h2270
        · linarith only [h0, h2209, h2270, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2272 | h2272
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2273 | h2273
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2274 | h2274
              · linarith only [h0, h2209, h2269, h2274, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2276 | h2276
                · linarith only [h0, h1, h2267, h2276, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h2276, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2279 | h2279
              · linarith only [h0, h1, h2269, h2273, h2279, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2281 | h2281
                · linarith only [h2267, h2281, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1, h2281, hc12, hlam, hphi, u2elo2]
          · linarith only [h0, h1, h2269, h2272, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2285 | h2285
        · linarith only [h0, h2209, h2285, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2287 | h2287
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2288 | h2288
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2289 | h2289
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2290 | h2290
                · linarith only [h0, h1, h2267, h2290, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h2290, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2293 | h2293
                · linarith only [h0, h1, h2267, h2287, h2293, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h1, h2293, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2296 | h2296
              · linarith only [h2287, h2288, h2296, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2298 | h2298
                · linarith only [h0, h1, h2288, h2298, hc23, hc35, hlam, hphi]
                · linarith only [h0, h1, h2298, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2301 | h2301
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2302 | h2302
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2303 | h2303
                · linarith only [h0, h1, h2287, h2303, hc23, hc34, hlam, hphi]
                · linarith only [h0, h1, h2303, hc12, hlam, hphi, u2elo2]
              · linarith only [h2287, h2301, h2302, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2307 | h2307
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2308 | h2308
                · linarith only [h0, h1, h2301, h2308, hc23, hc35, hlam, hphi]
                · linarith only [h0, h1, h2308, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2311 | h2311
                · linarith only [h0, h1, h2301, h2311, hc23, hc35, hlam, hphi]
                · linarith only [h0, h1, h2311, hc12, hlam, hphi, u2elo2]

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0_x0 m hb2 hb3 hb5 h0 h1
  · exact r1l7_22_13_15_M_LI_L_I_L_I_x0_x1 m hb2 hb3 hb5 h0 h1

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x1_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2314 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2315 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2316 | h2316
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2317 | h2317
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2318 | h2318
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2319 | h2319
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2320 | h2320
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2321 | h2321
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2322 | h2322
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2323 | h2323
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2324 | h2324
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2325 | h2325
                    · linarith only [h0, h2314, h2325, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h2314, h2319, h2322, h2325, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2324, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2314, h2317, h2319, h2323, hlam]
              · linarith only [h0, h2322, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2331 | h2331
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2332 | h2332
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2333 | h2333
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2334 | h2334
                    · linarith only [h0, h2314, h2334, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h2314, h2319, h2334, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2333, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2314, h2317, h2320, h2321, h2332, hlam]
              · linarith only [h0, h2331, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2340 | h2340
            · linarith only [h2319, h2320, h2340, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2342 | h2342
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2343 | h2343
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2344 | h2344
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2345 | h2345
                    · linarith only [h0, h2314, h2345, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h2319, h2320, h2342, h2345, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h2344, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2314, h2317, h2342, h2343, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h2342, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2351 | h2351
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2352 | h2352
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2353 | h2353
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2354 | h2354
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2355 | h2355
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2356 | h2356
                    · linarith only [h0, h2314, h2319, h2356, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2358 | h2358
                      · linarith only [h0, h2314, h2358, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h0, h2314, h2351, h2353, h2358, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2355, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2317, h2354, hlam]
              · linarith only [h0, h2314, h2353, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h2319, h2351, h2352, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2365 | h2365
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2366 | h2366
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2367 | h2367
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2368 | h2368
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2369 | h2369
                    · linarith only [h0, h2314, h2319, h2369, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2371 | h2371
                      · linarith only [h0, h2314, h2351, h2371, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2373 | h2373
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2374 | h2374
                          · linarith only [h0, h2316, h2319, h2374, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2376 | h2376
                            · linarith only [h2314, h2351, h2366, h2376, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2378 | h2378
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2379 | h2379
                                · rcases h2bigk with h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h0, hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    rcases p2380_3 (m.d 0 2) (by simp) with h2383 | h2383
                                    · rcases p2380_3 (m.d 1 2) (by simp) with h2384 | h2384
                                      · rcases p2380_3 (m.d 2 3) (by simp) with h2385 | h2385
                                        · linarith only [h2385, hlam, p2380_0]
                                        · rcases p2380_3 (m.d 2 4) (by simp) with h2387 | h2387
                                          · linarith only [h2317, h2387, hlam]
                                          · linarith only [h2374, h2387, hlam]
                                      · linarith only [h2366, h2384, hlam]
                                    · linarith only [h2383, hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h0, h2378, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, u2elo1]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    rcases p2380_3 (m.d 0 2) (by simp) with h2393 | h2393
                                    · rcases p2380_3 (m.d 1 2) (by simp) with h2394 | h2394
                                      · rcases p2380_3 (m.d 2 3) (by simp) with h2395 | h2395
                                        · linarith only [h2316, h2395, hlam]
                                        · rcases p2380_3 (m.d 2 4) (by simp) with h2397 | h2397
                                          · linarith only [h2317, h2397, hlam]
                                          · linarith only [h2378, h2397, hlam]
                                      · linarith only [h2368, h2394, hlam]
                                    · linarith only [h2393, hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2380_1, u2elo1]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    rcases p2380_3 (m.d 0 2) (by simp) with h2404 | h2404
                                    · linarith only [h0, h2404, hlam]
                                    · linarith only [h2316, h2404, hlam]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h2378, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, u2elo1]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    rcases p2380_3 (m.d 0 2) (by simp) with h2408 | h2408
                                    · linarith only [h0, h2408, hlam]
                                    · linarith only [h2318, h2408, hlam]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h2316, hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h2366, hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h2374, hlam, p2380_1]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h2376, hlam, p2380_1]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h2317, hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h2367, hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h2317, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2380_1, u2elo0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h0, h2317, h2376, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2380_1, u2elo1]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h2318, hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h2368, hlam, p2380_0]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h0, h2315, h2368, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2380_1, u2elo1]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [h2378, hlam, p2380_1]
                                  · have p2380_0 := h2380c.1
                                    have p2380_1 := h2380c.2.1
                                    have p2380_2 := h2380c.2.2.1
                                    have p2380_3 := h2380c.2.2.2
                                    linarith only [hlam, p2380_0]
                                · linarith only [h2319, h2365, h2379, hlam]
                              · linarith only [h0, h2315, h2373, h2378, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2428 | h2428
                          · linarith only [h2319, h2365, h2366, h2369, h2373, h2428, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2430 | h2430
                            · linarith only [h2351, h2365, h2366, h2369, h2373, h2430, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2432 | h2432
                              · linarith only [h0, h2317, h2366, h2369, h2373, h2432, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2434 | h2434
                                · rcases h2bigk with h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c | h2435c
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h0, hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    rcases p2435_3 (m.d 0 2) (by simp) with h2438 | h2438
                                    · rcases p2435_3 (m.d 1 2) (by simp) with h2439 | h2439
                                      · rcases p2435_3 (m.d 2 3) (by simp) with h2440 | h2440
                                        · linarith only [h2440, hlam, p2435_0]
                                        · rcases p2435_3 (m.d 2 4) (by simp) with h2442 | h2442
                                          · linarith only [h2317, h2442, hlam]
                                          · linarith only [h2428, h2442, hlam]
                                      · linarith only [h2366, h2439, hlam]
                                    · linarith only [h2438, hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    rcases p2435_3 (m.d 0 2) (by simp) with h2447 | h2447
                                    · rcases p2435_3 (m.d 1 2) (by simp) with h2448 | h2448
                                      · rcases p2435_3 (m.d 2 3) (by simp) with h2449 | h2449
                                        · linarith only [h2316, h2449, hlam]
                                        · rcases p2435_3 (m.d 2 4) (by simp) with h2451 | h2451
                                          · linarith only [h2451, hlam, p2435_0]
                                          · rcases p2435_3 (m.d 2 5) (by simp) with h2453 | h2453
                                            · linarith only [h2318, h2453, hlam]
                                            · linarith only [h2432, h2453, hlam]
                                      · linarith only [h2367, h2448, hlam]
                                    · linarith only [h2447, hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    rcases p2435_3 (m.d 0 2) (by simp) with h2458 | h2458
                                    · rcases p2435_3 (m.d 1 2) (by simp) with h2459 | h2459
                                      · rcases p2435_3 (m.d 2 3) (by simp) with h2460 | h2460
                                        · linarith only [h2316, h2460, hlam]
                                        · rcases p2435_3 (m.d 2 4) (by simp) with h2462 | h2462
                                          · linarith only [h2317, h2462, hlam]
                                          · rcases p2435_3 (m.d 2 5) (by simp) with h2464 | h2464
                                            · linarith only [h2464, hlam, p2435_0]
                                            · rcases h3bigk with h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c | h2466c
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [hlam, p2466_0]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h0, h2314, h2366, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2466_1, u2elo1]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h0, h2314, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2466_1, u2elo1]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h2319, hlam, p2466_0]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h2351, hlam, p2466_0]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h2314, hlam, p2466_0]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [hlam, p2466_0]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h2365, h2369, h2373, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2466_1]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h2369, hlam, p2466_0]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h2371, hlam, p2466_0]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h2316, hlam, p2466_1]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h2366, hlam, p2466_1]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [hlam, p2466_0]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h2428, hlam, p2466_0]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h2430, hlam, p2466_0]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                rcases p2466_3 (m.d 0 3) (by simp) with h2482 | h2482
                                                · linarith only [h2482, hlam, p2466_0]
                                                · rcases p2466_3 (m.d 1 3) (by simp) with h2484 | h2484
                                                  · linarith only [h2369, h2484, hlam]
                                                  · rcases p2466_3 (m.d 2 3) (by simp) with h2486 | h2486
                                                    · linarith only [h2428, h2486, hlam]
                                                    · rcases p2466_3 (m.d 3 4) (by simp) with h2488 | h2488
                                                      · rcases p2466_3 (m.d 3 5) (by simp) with h2489 | h2489
                                                        · linarith only [h2434, h2489, hlam]
                                                        · linarith only [h2351, h2489, hlam]
                                                      · linarith only [h2488, hlam, p2466_0]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                rcases p2466_3 (m.d 0 3) (by simp) with h2493 | h2493
                                                · linarith only [h2319, h2493, hlam]
                                                · linarith only [h2314, h2493, hlam]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                rcases p2466_3 (m.d 0 3) (by simp) with h2496 | h2496
                                                · linarith only [h2319, h2496, hlam]
                                                · linarith only [h2316, h2496, hlam]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [hlam, p2466_0]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h2351, h2365, h2366, h2369, h2373, hc23, hc34, hlam, hphi, p2466_1]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                rcases p2466_3 (m.d 0 3) (by simp) with h2501 | h2501
                                                · linarith only [h2501, hlam, p2466_0]
                                                · rcases p2466_3 (m.d 1 3) (by simp) with h2503 | h2503
                                                  · linarith only [h2371, h2503, hlam]
                                                  · rcases p2466_3 (m.d 2 3) (by simp) with h2505 | h2505
                                                    · linarith only [h2430, h2505, hlam]
                                                    · rcases p2466_3 (m.d 3 4) (by simp) with h2507 | h2507
                                                      · rcases p2466_3 (m.d 3 5) (by simp) with h2508 | h2508
                                                        · rcases h5bigk with h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c | h2509c
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [hlam, p2509_0]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h0, h2315, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2509_1, u2elo1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h0, h2315, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2509_1, u2elo1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h2351, hlam, p2509_0]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h0, h2315, h2373, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2509_1, u2elo1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h2315, hlam, p2509_0]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [hlam, p2509_0]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h0, h2315, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2509_1, u2elo1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h2371, hlam, p2509_0]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h2373, hlam, p2509_0]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h2318, hlam, p2509_1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h2368, hlam, p2509_1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [hlam, p2509_0]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h2430, hlam, p2509_1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h2432, hlam, p2509_0]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h2365, h2366, h2369, h2373, hc23, hc35, hlam, hphi, p2509_1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            rcases p2509_3 (m.d 0 5) (by simp) with h2526 | h2526
                                                            · linarith only [h2351, h2526, hlam]
                                                            · linarith only [h2315, h2526, hlam]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            rcases p2509_3 (m.d 0 5) (by simp) with h2529 | h2529
                                                            · linarith only [h2351, h2529, hlam]
                                                            · linarith only [h2318, h2529, hlam]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [hlam, p2509_0]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h2366, h2369, h2373, h2434, hc23, hc34, hlam, hphi, p2509_1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h2365, hlam, p2509_1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h0, h2315, h2365, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p2509_1, u2elo1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h0, h2315, h2365, h2428, h2432, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2509_1, u2elo1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [h2434, hlam, p2509_1]
                                                          · have p2509_0 := h2509c.1
                                                            have p2509_1 := h2509c.2.1
                                                            have p2509_2 := h2509c.2.2.1
                                                            have p2509_3 := h2509c.2.2.2
                                                            linarith only [hlam, p2509_0]
                                                        · linarith only [h2508, hlam, p2466_0]
                                                      · linarith only [h2319, h2507, hlam]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                rcases p2466_3 (m.d 0 3) (by simp) with h2541 | h2541
                                                · linarith only [h2351, h2541, hlam]
                                                · linarith only [h2314, h2541, hlam]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                rcases p2466_3 (m.d 0 3) (by simp) with h2544 | h2544
                                                · linarith only [h2351, h2544, hlam]
                                                · linarith only [h2316, h2544, hlam]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [h2434, hlam, p2466_1]
                                              · have p2466_0 := h2466c.1
                                                have p2466_1 := h2466c.2.1
                                                have p2466_2 := h2466c.2.2.1
                                                have p2466_3 := h2466c.2.2.2
                                                linarith only [hlam, p2466_0]
                                      · linarith only [h2368, h2459, hlam]
                                    · linarith only [h2458, hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2435_1, u2elo1]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    rcases p2435_3 (m.d 0 2) (by simp) with h2553 | h2553
                                    · linarith only [h0, h2553, hlam]
                                    · linarith only [h2316, h2553, hlam]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    rcases p2435_3 (m.d 0 2) (by simp) with h2556 | h2556
                                    · linarith only [h0, h2556, hlam]
                                    · linarith only [h2317, h2556, hlam]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    rcases p2435_3 (m.d 0 2) (by simp) with h2559 | h2559
                                    · linarith only [h0, h2559, hlam]
                                    · linarith only [h2318, h2559, hlam]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h2316, hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h2366, hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h2428, hlam, p2435_1]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h2430, hlam, p2435_1]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h2317, hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h2367, hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h0, h2315, h2368, h2432, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2435_1, u2elo1]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h2432, hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h2318, hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h2368, hlam, p2435_0]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h0, h2315, h2368, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2435_1, u2elo1]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [h0, h2315, h2368, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2435_1, u2elo1]
                                  · have p2435_0 := h2435c.1
                                    have p2435_1 := h2435c.2.1
                                    have p2435_2 := h2435c.2.2.1
                                    have p2435_3 := h2435c.2.2.2
                                    linarith only [hlam, p2435_0]
                                · linarith only [h2314, h2317, h2319, h2365, h2366, h2434, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h0, h2368, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2367, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h2314, h2366, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2581 | h2581
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2582 | h2582
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2583 | h2583
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2584 | h2584
                    · linarith only [h0, h2314, h2584, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2586 | h2586
                      · linarith only [h0, h2314, h2586, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2588 | h2588
                        · linarith only [h0, h2315, h2319, h2365, h2588, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2590 | h2590
                          · linarith only [h2314, h2319, h2581, h2590, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2592 | h2592
                            · linarith only [h0, h2314, h2351, h2581, h2592, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2594 | h2594
                              · linarith only [h0, h2315, h2582, h2588, h2594, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2596 | h2596
                                · rcases h2bigk with h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h0, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    rcases p2597_3 (m.d 0 2) (by simp) with h2600 | h2600
                                    · rcases p2597_3 (m.d 1 2) (by simp) with h2601 | h2601
                                      · rcases p2597_3 (m.d 2 3) (by simp) with h2602 | h2602
                                        · linarith only [h2602, hlam, p2597_0]
                                        · rcases p2597_3 (m.d 2 4) (by simp) with h2604 | h2604
                                          · linarith only [h2317, h2604, hlam]
                                          · linarith only [h2590, h2604, hlam]
                                      · linarith only [h2581, h2601, hlam]
                                    · linarith only [h2600, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    rcases p2597_3 (m.d 0 2) (by simp) with h2609 | h2609
                                    · rcases p2597_3 (m.d 1 2) (by simp) with h2610 | h2610
                                      · rcases p2597_3 (m.d 2 3) (by simp) with h2611 | h2611
                                        · linarith only [h2316, h2611, hlam]
                                        · rcases p2597_3 (m.d 2 4) (by simp) with h2613 | h2613
                                          · linarith only [h2613, hlam, p2597_0]
                                          · rcases p2597_3 (m.d 2 5) (by simp) with h2615 | h2615
                                            · linarith only [h2318, h2615, hlam]
                                            · linarith only [h2594, h2615, hlam]
                                      · linarith only [h2582, h2610, hlam]
                                    · linarith only [h2609, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    rcases p2597_3 (m.d 0 2) (by simp) with h2620 | h2620
                                    · rcases p2597_3 (m.d 1 2) (by simp) with h2621 | h2621
                                      · rcases p2597_3 (m.d 2 3) (by simp) with h2622 | h2622
                                        · linarith only [h2316, h2622, hlam]
                                        · rcases p2597_3 (m.d 2 4) (by simp) with h2624 | h2624
                                          · linarith only [h2317, h2624, hlam]
                                          · rcases p2597_3 (m.d 2 5) (by simp) with h2626 | h2626
                                            · linarith only [h2626, hlam, p2597_0]
                                            · rcases h3bigk with h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [hlam, p2628_0]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h0, h2314, h2581, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2628_1, u2elo1]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h0, h2314, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2628_1, u2elo1]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h2319, hlam, p2628_0]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h2351, hlam, p2628_0]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h2314, hlam, p2628_0]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [hlam, p2628_0]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h0, h2314, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2628_1, u2elo1]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h2584, hlam, p2628_0]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h2586, hlam, p2628_0]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h2316, hlam, p2628_1]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h2581, hlam, p2628_1]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [hlam, p2628_0]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h2590, hlam, p2628_0]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h2592, hlam, p2628_0]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                rcases p2628_3 (m.d 0 3) (by simp) with h2644 | h2644
                                                · linarith only [h2644, hlam, p2628_0]
                                                · rcases p2628_3 (m.d 1 3) (by simp) with h2646 | h2646
                                                  · linarith only [h2584, h2646, hlam]
                                                  · rcases p2628_3 (m.d 2 3) (by simp) with h2648 | h2648
                                                    · linarith only [h2590, h2648, hlam]
                                                    · rcases p2628_3 (m.d 3 4) (by simp) with h2650 | h2650
                                                      · rcases p2628_3 (m.d 3 5) (by simp) with h2651 | h2651
                                                        · linarith only [h2596, h2651, hlam]
                                                        · linarith only [h2351, h2651, hlam]
                                                      · linarith only [h2650, hlam, p2628_0]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                rcases p2628_3 (m.d 0 3) (by simp) with h2655 | h2655
                                                · linarith only [h2319, h2655, hlam]
                                                · linarith only [h2314, h2655, hlam]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                rcases p2628_3 (m.d 0 3) (by simp) with h2658 | h2658
                                                · linarith only [h2319, h2658, hlam]
                                                · linarith only [h2316, h2658, hlam]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [hlam, p2628_0]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h2319, h2365, h2596, hc03, hc34, hlam, hphi, p2628_1]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                rcases p2628_3 (m.d 0 3) (by simp) with h2663 | h2663
                                                · linarith only [h2663, hlam, p2628_0]
                                                · rcases p2628_3 (m.d 1 3) (by simp) with h2665 | h2665
                                                  · linarith only [h2586, h2665, hlam]
                                                  · rcases p2628_3 (m.d 2 3) (by simp) with h2667 | h2667
                                                    · linarith only [h2592, h2667, hlam]
                                                    · rcases p2628_3 (m.d 3 4) (by simp) with h2669 | h2669
                                                      · rcases p2628_3 (m.d 3 5) (by simp) with h2670 | h2670
                                                        · rcases h5bigk with h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c | h2671c
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [hlam, p2671_0]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h0, h2315, h2581, h2584, h2588, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2671_1, u2elo1]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h0, h2315, h2594, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2671_1, u2elo1]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2351, hlam, p2671_0]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2365, hlam, p2671_0]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2315, hlam, p2671_0]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [hlam, p2671_0]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h0, h2315, h2594, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2671_1, u2elo1]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2586, hlam, p2671_0]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2588, hlam, p2671_0]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2318, hlam, p2671_1]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2583, hlam, p2671_1]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [hlam, p2671_0]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2592, hlam, p2671_1]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2594, hlam, p2671_0]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            rcases p2671_3 (m.d 0 5) (by simp) with h2687 | h2687
                                                            · linarith only [h2351, h2687, hlam]
                                                            · rcases p2671_3 (m.d 1 5) (by simp) with h2689 | h2689
                                                              · linarith only [h2586, h2689, hlam]
                                                              · rcases p2671_3 (m.d 2 5) (by simp) with h2691 | h2691
                                                                · linarith only [h2592, h2691, hlam]
                                                                · rcases p2671_3 (m.d 3 5) (by simp) with h2693 | h2693
                                                                  · rcases p2671_3 (m.d 4 5) (by simp) with h2694 | h2694
                                                                    · linarith only [h2596, h2694, hlam]
                                                                    · linarith only [h2365, h2694, hlam]
                                                                  · linarith only [h2351, h2693, hlam]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            rcases p2671_3 (m.d 0 5) (by simp) with h2698 | h2698
                                                            · linarith only [h2351, h2698, hlam]
                                                            · linarith only [h2315, h2698, hlam]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            rcases p2671_3 (m.d 0 5) (by simp) with h2701 | h2701
                                                            · linarith only [h2351, h2701, hlam]
                                                            · linarith only [h2318, h2701, hlam]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [hlam, p2671_0]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2314, h2319, h2365, h2581, h2596, hc23, hc34, hlam, hphi, p2671_1]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2318, h2590, h2594, h2596, hc23, hc34, hlam, hphi, p2671_1]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2583, h2590, h2594, h2596, hc23, hc34, hlam, hphi, p2671_1]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2590, h2594, h2596, hc23, hc34, hlam, hphi, p2671_1]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [h2596, hlam, p2671_1]
                                                          · have p2671_0 := h2671c.1
                                                            have p2671_1 := h2671c.2.1
                                                            have p2671_2 := h2671c.2.2.1
                                                            have p2671_3 := h2671c.2.2.2
                                                            linarith only [hlam, p2671_0]
                                                        · linarith only [h2670, hlam, p2628_0]
                                                      · linarith only [h2319, h2669, hlam]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                rcases p2628_3 (m.d 0 3) (by simp) with h2713 | h2713
                                                · linarith only [h2351, h2713, hlam]
                                                · linarith only [h2314, h2713, hlam]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                rcases p2628_3 (m.d 0 3) (by simp) with h2716 | h2716
                                                · linarith only [h2351, h2716, hlam]
                                                · linarith only [h2316, h2716, hlam]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [h2596, hlam, p2628_1]
                                              · have p2628_0 := h2628c.1
                                                have p2628_1 := h2628c.2.1
                                                have p2628_2 := h2628c.2.2.1
                                                have p2628_3 := h2628c.2.2.2
                                                linarith only [hlam, p2628_0]
                                      · linarith only [h2583, h2621, hlam]
                                    · linarith only [h2620, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2597_1, u2elo1]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    rcases p2597_3 (m.d 0 2) (by simp) with h2725 | h2725
                                    · linarith only [h0, h2725, hlam]
                                    · linarith only [h2316, h2725, hlam]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    rcases p2597_3 (m.d 0 2) (by simp) with h2728 | h2728
                                    · linarith only [h0, h2728, hlam]
                                    · linarith only [h2317, h2728, hlam]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    rcases p2597_3 (m.d 0 2) (by simp) with h2731 | h2731
                                    · linarith only [h0, h2731, hlam]
                                    · linarith only [h2318, h2731, hlam]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2316, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2581, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2590, hlam, p2597_1]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2592, hlam, p2597_1]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2317, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2582, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h0, h2315, h2583, h2594, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2597_1, u2elo0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2594, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2318, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2583, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h0, h2315, h2583, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2597_1, u2elo1]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h0, h2315, h2583, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2597_1, u2elo1]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [hlam, p2597_0]
                                · rcases h2bigk with h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c | h2749c
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h0, hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    rcases p2749_3 (m.d 0 2) (by simp) with h2752 | h2752
                                    · rcases p2749_3 (m.d 1 2) (by simp) with h2753 | h2753
                                      · rcases p2749_3 (m.d 2 3) (by simp) with h2754 | h2754
                                        · linarith only [h2754, hlam, p2749_0]
                                        · rcases p2749_3 (m.d 2 4) (by simp) with h2756 | h2756
                                          · linarith only [h2317, h2756, hlam]
                                          · linarith only [h2590, h2756, hlam]
                                      · linarith only [h2581, h2753, hlam]
                                    · linarith only [h2752, hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    rcases p2749_3 (m.d 0 2) (by simp) with h2761 | h2761
                                    · rcases p2749_3 (m.d 1 2) (by simp) with h2762 | h2762
                                      · rcases p2749_3 (m.d 2 3) (by simp) with h2763 | h2763
                                        · linarith only [h2316, h2763, hlam]
                                        · rcases p2749_3 (m.d 2 4) (by simp) with h2765 | h2765
                                          · linarith only [h2765, hlam, p2749_0]
                                          · rcases p2749_3 (m.d 2 5) (by simp) with h2767 | h2767
                                            · linarith only [h2318, h2767, hlam]
                                            · linarith only [h2594, h2767, hlam]
                                      · linarith only [h2582, h2762, hlam]
                                    · linarith only [h2761, hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    rcases p2749_3 (m.d 0 2) (by simp) with h2772 | h2772
                                    · rcases p2749_3 (m.d 1 2) (by simp) with h2773 | h2773
                                      · rcases p2749_3 (m.d 2 3) (by simp) with h2774 | h2774
                                        · linarith only [h2316, h2774, hlam]
                                        · rcases p2749_3 (m.d 2 4) (by simp) with h2776 | h2776
                                          · linarith only [h2317, h2776, hlam]
                                          · rcases p2749_3 (m.d 2 5) (by simp) with h2778 | h2778
                                            · linarith only [h2778, hlam, p2749_0]
                                            · rcases h3bigk with h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [hlam, p2780_0]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2319, h2581, hc23, hc34, hlam, hphi, p2780_1]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2319, h2596, hc23, hc45, hlam, hphi, ht34, p2780_1]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2319, hlam, p2780_0]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2351, hlam, p2780_0]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2314, hlam, p2780_0]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [hlam, p2780_0]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h0, h2314, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2780_1, u2elo1]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2584, hlam, p2780_0]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2586, hlam, p2780_0]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2316, hlam, p2780_1]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2581, hlam, p2780_1]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [hlam, p2780_0]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2590, hlam, p2780_0]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2592, hlam, p2780_0]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2596, hc03, hc45, hlam, hphi, ht34, p2780_1]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2596, hc13, hc45, hlam, hphi, ht34, p2780_1]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2596, hc23, hc45, hlam, hphi, ht34, p2780_1]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [hlam, p2780_0]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2596, hlam, p2780_0]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                rcases p2780_3 (m.d 0 3) (by simp) with h2801 | h2801
                                                · linarith only [h2801, hlam, p2780_0]
                                                · rcases p2780_3 (m.d 1 3) (by simp) with h2803 | h2803
                                                  · linarith only [h2586, h2803, hlam]
                                                  · rcases p2780_3 (m.d 2 3) (by simp) with h2805 | h2805
                                                    · linarith only [h2592, h2805, hlam]
                                                    · rcases p2780_3 (m.d 3 4) (by simp) with h2807 | h2807
                                                      · linarith only [h2596, h2807, hlam]
                                                      · linarith only [h2319, h2807, hlam]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                rcases p2780_3 (m.d 0 3) (by simp) with h2810 | h2810
                                                · linarith only [h2351, h2810, hlam]
                                                · linarith only [h2314, h2810, hlam]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                rcases p2780_3 (m.d 0 3) (by simp) with h2813 | h2813
                                                · linarith only [h2351, h2813, hlam]
                                                · linarith only [h2316, h2813, hlam]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [h2314, h2319, h2581, h2596, hc23, hc45, hlam, hphi, ht34, p2780_1]
                                              · have p2780_0 := h2780c.1
                                                have p2780_1 := h2780c.2.1
                                                have p2780_2 := h2780c.2.2.1
                                                have p2780_3 := h2780c.2.2.2
                                                linarith only [hlam, p2780_0]
                                      · linarith only [h2583, h2773, hlam]
                                    · linarith only [h2772, hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [hc02, hlam, hphi, p2749_1, u2elo1]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    rcases p2749_3 (m.d 0 2) (by simp) with h2822 | h2822
                                    · linarith only [h0, h2822, hlam]
                                    · linarith only [h2316, h2822, hlam]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    rcases p2749_3 (m.d 0 2) (by simp) with h2825 | h2825
                                    · linarith only [h0, h2825, hlam]
                                    · linarith only [h2317, h2825, hlam]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    rcases p2749_3 (m.d 0 2) (by simp) with h2828 | h2828
                                    · linarith only [h0, h2828, hlam]
                                    · linarith only [h2318, h2828, hlam]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h2316, hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h2581, hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h2590, hlam, p2749_1]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h2592, hlam, p2749_1]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h2317, hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h2582, hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h2317, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2749_1, u2elo0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h2594, hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h2318, hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h2583, hlam, p2749_0]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h0, h2315, h2583, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2749_1, u2elo1]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [h0, h2315, h2583, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2749_1, u2elo1]
                                  · have p2749_0 := h2749c.1
                                    have p2749_1 := h2749c.2.1
                                    have p2749_2 := h2749c.2.2.1
                                    have p2749_3 := h2749c.2.2.2
                                    linarith only [hlam, p2749_0]
                  · linarith only [h0, h2583, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2582, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h2314, h2581, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · linarith only [h0, h2315, h2318, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2850 | h2850
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2851 | h2851
        · linarith only [h0, h2314, h2317, h2851, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2853 | h2853
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2854 | h2854
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2855 | h2855
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2856 | h2856
                · linarith only [h0, h2317, h2856, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2314, h2855, h2856, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2314, h2855, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h0, h2314, h2317, h2853, h2854, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2861 | h2861
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2862 | h2862
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2863 | h2863
                · linarith only [h0, h2314, h2317, h2862, h2863, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h2314, h2862, h2863, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h2862, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h0, h2315, h2317, h2861, hlam]
      · linarith only [h0, h2315, h2850, hlam]
  · linarith only [h0, h2314, h2316, hlam]

end R2N4
