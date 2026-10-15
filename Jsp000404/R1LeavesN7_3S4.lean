import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1951 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2201 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2272 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2273 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h2274 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1bigk := hb1.1
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
  have h9 := hg9
  rcases m.htr 2 3 4 (by decide) (by decide) with h2275 | h2275
  · rcases m.htr 2 3 5 (by decide) (by decide) with h2276 | h2276
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2277 | h2277
      · rcases m.htr 3 4 5 (by decide) (by decide) with h2278 | h2278
        · rcases h1bigk with h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c | h2279c
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            rcases p2279_3 (m.d 0 1) (by simp) with h2281 | h2281
            · rcases p2279_3 (m.d 1 2) (by simp) with h2282 | h2282
              · linarith only [h2282, hlam, p2279_0]
              · rcases p2279_3 (m.d 1 3) (by simp) with h2284 | h2284
                · linarith only [h1, h2284, hlam]
                · linarith only [h10, h2284, hlam]
            · linarith only [h2281, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [h2272, h2278, hc01, hc45, hlam, hphi, ht0b, ht5b, p2279_1]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            rcases p2279_3 (m.d 0 1) (by simp) with h2289 | h2289
            · rcases p2279_3 (m.d 1 2) (by simp) with h2290 | h2290
              · linarith only [h0, h2290, hlam]
              · rcases p2279_3 (m.d 1 3) (by simp) with h2292 | h2292
                · linarith only [h1, h2292, hlam]
                · linarith only [h2272, h2292, hlam]
            · linarith only [h2289, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            rcases p2279_3 (m.d 0 1) (by simp) with h2296 | h2296
            · rcases p2279_3 (m.d 1 2) (by simp) with h2297 | h2297
              · linarith only [h0, h2297, hlam]
              · rcases p2279_3 (m.d 1 3) (by simp) with h2299 | h2299
                · linarith only [h1, h2299, hlam]
                · linarith only [h2273, h2299, hlam]
            · linarith only [h2296, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [h0, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [h10, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [h1951, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [h2201, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [h1, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            rcases p2279_3 (m.d 0 1) (by simp) with h2309 | h2309
            · rcases p2279_3 (m.d 1 2) (by simp) with h2310 | h2310
              · linarith only [h10, h2310, hlam]
              · rcases p2279_3 (m.d 1 3) (by simp) with h2312 | h2312
                · rcases p2279_3 (m.d 1 4) (by simp) with h2313 | h2313
                  · linarith only [h2272, h2313, hlam]
                  · linarith only [h1951, h2313, hlam]
                · linarith only [h10, h2312, hlam]
            · linarith only [h0, h2309, hlam]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [h0, h10, h2272, h2278, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2279_1]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            rcases p2279_3 (m.d 0 1) (by simp) with h2320 | h2320
            · rcases p2279_3 (m.d 1 2) (by simp) with h2321 | h2321
              · linarith only [h10, h2321, hlam]
              · rcases p2279_3 (m.d 1 3) (by simp) with h2323 | h2323
                · rcases p2279_3 (m.d 1 4) (by simp) with h2324 | h2324
                  · linarith only [h2272, h2324, hlam]
                  · linarith only [h2274, h2324, hlam]
                · linarith only [h2273, h2323, hlam]
            · linarith only [h2320, h3, hlam]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [h2, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            rcases p2279_3 (m.d 0 1) (by simp) with h2330 | h2330
            · rcases p2279_3 (m.d 1 2) (by simp) with h2331 | h2331
              · linarith only [h1951, h2331, hlam]
              · rcases p2279_3 (m.d 1 3) (by simp) with h2333 | h2333
                · rcases p2279_3 (m.d 1 4) (by simp) with h2334 | h2334
                  · rcases p2279_3 (m.d 1 5) (by simp) with h2335 | h2335
                    · linarith only [h2274, h2335, hlam]
                    · linarith only [h2201, h2335, hlam]
                  · linarith only [h1951, h2334, hlam]
                · linarith only [h10, h2333, hlam]
            · linarith only [h0, h2330, hlam]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [h2272, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            rcases p2279_3 (m.d 0 1) (by simp) with h2343 | h2343
            · rcases p2279_3 (m.d 1 2) (by simp) with h2344 | h2344
              · linarith only [h1951, h2344, hlam]
              · rcases p2279_3 (m.d 1 3) (by simp) with h2346 | h2346
                · rcases p2279_3 (m.d 1 4) (by simp) with h2347 | h2347
                  · rcases p2279_3 (m.d 1 5) (by simp) with h2348 | h2348
                    · linarith only [h2274, h2348, hlam]
                    · rcases h3bigk with h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h0, h2201, h2272, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2279_1, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h0, h10, h2201, h2272, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2279_1, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        rcases p2350_3 (m.d 0 3) (by simp) with h2354 | h2354
                        · rcases p2350_3 (m.d 1 3) (by simp) with h2355 | h2355
                          · linarith only [h1, h2355, hlam]
                          · linarith only [h2272, h2355, hlam]
                        · linarith only [h2354, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        rcases p2350_3 (m.d 0 3) (by simp) with h2359 | h2359
                        · rcases p2350_3 (m.d 1 3) (by simp) with h2360 | h2360
                          · linarith only [h1, h2360, hlam]
                          · linarith only [h2273, h2360, hlam]
                        · linarith only [h2359, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h1, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h10, hlam, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h1, h2278, hc01, hc45, hlam, hphi, ht0b, ht5b, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        rcases p2350_3 (m.d 0 3) (by simp) with h2368 | h2368
                        · rcases p2350_3 (m.d 1 3) (by simp) with h2369 | h2369
                          · rcases p2350_3 (m.d 2 3) (by simp) with h2370 | h2370
                            · rcases p2350_3 (m.d 3 4) (by simp) with h2371 | h2371
                              · linarith only [h2272, h2371, hlam]
                              · linarith only [h2278, h2371, hlam]
                            · linarith only [h2276, h2370, hlam]
                          · linarith only [h2369, hlam, p2350_0]
                        · linarith only [h2368, h8, hlam]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h4, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h0, h2272, h2278, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h0, h2278, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        rcases p2350_3 (m.d 0 3) (by simp) with h2381 | h2381
                        · rcases p2350_3 (m.d 1 3) (by simp) with h2382 | h2382
                          · linarith only [h10, h2382, hlam]
                          · linarith only [h2273, h2382, hlam]
                        · linarith only [h2381, h8, hlam]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h7, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h2272, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h2275, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h1, h2272, hc01, hc35, hlam, hphi, ht0b, ht5b, p2350_1]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h8, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h2273, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h2276, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [h2278, hlam, p2350_0]
                      · have p2350_0 := h2350c.1
                        have p2350_1 := h2350c.2.1
                        have p2350_2 := h2350c.2.2.1
                        have p2350_3 := h2350c.2.2.2
                        linarith only [hlam, p2350_0]
                  · linarith only [h2274, h2347, hlam]
                · linarith only [h2273, h2346, hlam]
            · linarith only [h2343, h3, hlam]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [h3, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            rcases p2279_3 (m.d 0 1) (by simp) with h2400 | h2400
            · rcases p2279_3 (m.d 1 2) (by simp) with h2401 | h2401
              · linarith only [h2201, h2401, hlam]
              · rcases p2279_3 (m.d 1 3) (by simp) with h2403 | h2403
                · rcases p2279_3 (m.d 1 4) (by simp) with h2404 | h2404
                  · rcases p2279_3 (m.d 1 5) (by simp) with h2405 | h2405
                    · rcases h3bigk with h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h2273, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2279_1, p2406_1]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h0, h10, h2273, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2279_1, p2406_1]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        rcases p2406_3 (m.d 0 3) (by simp) with h2410 | h2410
                        · rcases p2406_3 (m.d 1 3) (by simp) with h2411 | h2411
                          · linarith only [h1, h2411, hlam]
                          · linarith only [h2272, h2411, hlam]
                        · linarith only [h2410, hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        rcases p2406_3 (m.d 0 3) (by simp) with h2415 | h2415
                        · rcases p2406_3 (m.d 1 3) (by simp) with h2416 | h2416
                          · linarith only [h1, h2416, hlam]
                          · linarith only [h2273, h2416, hlam]
                        · linarith only [h2415, hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h1, hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h10, hlam, p2406_1]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h1, h2278, hc01, hc45, hlam, hphi, ht0b, ht5b, p2406_1]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        rcases p2406_3 (m.d 0 3) (by simp) with h2424 | h2424
                        · rcases p2406_3 (m.d 1 3) (by simp) with h2425 | h2425
                          · rcases p2406_3 (m.d 2 3) (by simp) with h2426 | h2426
                            · rcases p2406_3 (m.d 3 4) (by simp) with h2427 | h2427
                              · linarith only [h2272, h2427, hlam]
                              · linarith only [h2278, h2427, hlam]
                            · linarith only [h2276, h2426, hlam]
                          · linarith only [h2425, hlam, p2406_0]
                        · linarith only [h2424, h8, hlam]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h4, hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h0, h2272, h2278, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2406_1]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h0, h2278, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2406_1]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        rcases p2406_3 (m.d 0 3) (by simp) with h2437 | h2437
                        · rcases p2406_3 (m.d 1 3) (by simp) with h2438 | h2438
                          · linarith only [h10, h2438, hlam]
                          · linarith only [h2273, h2438, hlam]
                        · linarith only [h2437, h8, hlam]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h7, hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h2272, hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h2275, hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h1, h2272, h2278, hc01, hc45, hlam, hphi, ht0b, ht5b, p2406_1]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h8, hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h2273, hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h2276, hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [h2278, hlam, p2406_0]
                      · have p2406_0 := h2406c.1
                        have p2406_1 := h2406c.2.1
                        have p2406_2 := h2406c.2.2.1
                        have p2406_3 := h2406c.2.2.2
                        linarith only [hlam, p2406_0]
                    · linarith only [h2201, h2405, hlam]
                  · linarith only [h1951, h2404, hlam]
                · linarith only [h10, h2403, hlam]
            · linarith only [h0, h2400, hlam]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [h2273, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [h2274, hlam, p2279_0]
          · have p2279_0 := h2279c.1
            have p2279_1 := h2279c.2.1
            have p2279_2 := h2279c.2.2.1
            have p2279_3 := h2279c.2.2.2
            linarith only [hlam, p2279_0]
        · rcases h1bigk with h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            rcases p2459_3 (m.d 0 1) (by simp) with h2461 | h2461
            · rcases p2459_3 (m.d 1 2) (by simp) with h2462 | h2462
              · linarith only [h2462, hlam, p2459_0]
              · rcases p2459_3 (m.d 1 3) (by simp) with h2464 | h2464
                · linarith only [h1, h2464, hlam]
                · linarith only [h10, h2464, hlam]
            · linarith only [h2461, hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h2272, h2274, h2278, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2459_1]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h2274, h2278, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2459_1]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            rcases p2459_3 (m.d 0 1) (by simp) with h2470 | h2470
            · rcases p2459_3 (m.d 1 2) (by simp) with h2471 | h2471
              · linarith only [h0, h2471, hlam]
              · rcases p2459_3 (m.d 1 3) (by simp) with h2473 | h2473
                · linarith only [h1, h2473, hlam]
                · linarith only [h2273, h2473, hlam]
            · linarith only [h2470, hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h0, hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h10, hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h1951, hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h2201, hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h1, hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            rcases p2459_3 (m.d 0 1) (by simp) with h2483 | h2483
            · rcases p2459_3 (m.d 1 2) (by simp) with h2484 | h2484
              · linarith only [h10, h2484, hlam]
              · rcases p2459_3 (m.d 1 3) (by simp) with h2486 | h2486
                · rcases p2459_3 (m.d 1 4) (by simp) with h2487 | h2487
                  · linarith only [h2272, h2487, hlam]
                  · linarith only [h1951, h2487, hlam]
                · linarith only [h10, h2486, hlam]
            · linarith only [h0, h2483, hlam]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h0, h10, h2274, h2278, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2459_1]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h0, h10, h2274, h2278, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2459_1]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h2, hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            rcases p2459_3 (m.d 0 1) (by simp) with h2496 | h2496
            · rcases p2459_3 (m.d 1 2) (by simp) with h2497 | h2497
              · linarith only [h1951, h2497, hlam]
              · rcases p2459_3 (m.d 1 3) (by simp) with h2499 | h2499
                · rcases p2459_3 (m.d 1 4) (by simp) with h2500 | h2500
                  · rcases p2459_3 (m.d 1 5) (by simp) with h2501 | h2501
                    · linarith only [h2274, h2501, hlam]
                    · linarith only [h2201, h2501, hlam]
                  · linarith only [h1951, h2500, hlam]
                · linarith only [h10, h2499, hlam]
            · linarith only [h0, h2496, hlam]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h2272, hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h0, h1951, h2274, h2275, h2278, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2459_1]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h3, hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            rcases p2459_3 (m.d 0 1) (by simp) with h2511 | h2511
            · rcases p2459_3 (m.d 1 2) (by simp) with h2512 | h2512
              · linarith only [h2201, h2512, hlam]
              · rcases p2459_3 (m.d 1 3) (by simp) with h2514 | h2514
                · rcases p2459_3 (m.d 1 4) (by simp) with h2515 | h2515
                  · rcases p2459_3 (m.d 1 5) (by simp) with h2516 | h2516
                    · rcases h3bigk with h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h0, h2273, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h0, h10, h2273, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        rcases p2517_3 (m.d 0 3) (by simp) with h2521 | h2521
                        · rcases p2517_3 (m.d 1 3) (by simp) with h2522 | h2522
                          · linarith only [h1, h2522, hlam]
                          · linarith only [h2272, h2522, hlam]
                        · linarith only [h2521, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        rcases p2517_3 (m.d 0 3) (by simp) with h2526 | h2526
                        · rcases p2517_3 (m.d 1 3) (by simp) with h2527 | h2527
                          · linarith only [h1, h2527, hlam]
                          · linarith only [h2273, h2527, hlam]
                        · linarith only [h2526, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h10, hlam, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        rcases p2517_3 (m.d 0 3) (by simp) with h2534 | h2534
                        · rcases p2517_3 (m.d 1 3) (by simp) with h2535 | h2535
                          · rcases p2517_3 (m.d 2 3) (by simp) with h2536 | h2536
                            · rcases p2517_3 (m.d 3 4) (by simp) with h2537 | h2537
                              · linarith only [h2537, hlam, p2517_0]
                              · rcases p2517_3 (m.d 3 5) (by simp) with h2539 | h2539
                                · linarith only [h2273, h2539, hlam]
                                · linarith only [h2278, h2539, hlam]
                            · linarith only [h2275, h2536, hlam]
                          · linarith only [h2535, hlam, p2517_0]
                        · linarith only [h2534, h7, hlam]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        rcases p2517_3 (m.d 0 3) (by simp) with h2545 | h2545
                        · rcases p2517_3 (m.d 1 3) (by simp) with h2546 | h2546
                          · rcases p2517_3 (m.d 2 3) (by simp) with h2547 | h2547
                            · rcases p2517_3 (m.d 3 4) (by simp) with h2548 | h2548
                              · linarith only [h2272, h2548, hlam]
                              · rcases p2517_3 (m.d 3 5) (by simp) with h2550 | h2550
                                · linarith only [h2550, hlam, p2517_0]
                                · rcases h5bigk with h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h0, h2201, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2459_1, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    rcases p2552_3 (m.d 0 5) (by simp) with h2556 | h2556
                                    · rcases p2552_3 (m.d 1 5) (by simp) with h2557 | h2557
                                      · linarith only [h2557, h3, hlam]
                                      · linarith only [h2273, h2557, hlam]
                                    · linarith only [h2556, h8, hlam]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h0, h2278, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h3, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2201, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h0, h10, h2272, h2274, h2278, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h6, hlam, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h0, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h0, h2276, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h0, h2275, h2277, h2278, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h8, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2273, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2276, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2278, hlam, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h9, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2274, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2277, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h0, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [hlam, p2552_0]
                            · linarith only [h2276, h2547, hlam]
                          · linarith only [h2546, hlam, p2517_0]
                        · linarith only [h2545, h8, hlam]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h4, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h0, h2272, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        rcases p2517_3 (m.d 0 3) (by simp) with h2588 | h2588
                        · rcases p2517_3 (m.d 1 3) (by simp) with h2589 | h2589
                          · linarith only [h10, h2589, hlam]
                          · linarith only [h2272, h2589, hlam]
                        · linarith only [h2588, h7, hlam]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        rcases p2517_3 (m.d 0 3) (by simp) with h2593 | h2593
                        · rcases p2517_3 (m.d 1 3) (by simp) with h2594 | h2594
                          · linarith only [h10, h2594, hlam]
                          · linarith only [h2273, h2594, hlam]
                        · linarith only [h2593, h8, hlam]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h7, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h2272, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h2275, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h2278, hlam, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h8, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h2273, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h2276, hlam, p2517_0]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [h1, h2273, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2517_1]
                      · have p2517_0 := h2517c.1
                        have p2517_1 := h2517c.2.1
                        have p2517_2 := h2517c.2.2.1
                        have p2517_3 := h2517c.2.2.2
                        linarith only [hlam, p2517_0]
                    · linarith only [h2201, h2516, hlam]
                  · linarith only [h1951, h2515, hlam]
                · linarith only [h10, h2514, hlam]
            · linarith only [h0, h2511, hlam]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h2273, hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [h2274, hlam, p2459_0]
          · have p2459_0 := h2459c.1
            have p2459_1 := h2459c.2.1
            have p2459_2 := h2459c.2.2.1
            have p2459_3 := h2459c.2.2.2
            linarith only [hlam, p2459_0]
      · linarith only [h1951, h2, h2274, h2277, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · linarith only [h10, h2273, h2276, hlam]
  · linarith only [h10, h2272, h2275, hlam]

end R2N4
