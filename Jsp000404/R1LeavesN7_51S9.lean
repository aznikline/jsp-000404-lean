import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_51S7
import Jsp000404.R1LeavesN7_51S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x1_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1403 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1593 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1700 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1701 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2289 | h2289
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2290 | h2290
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2291 | h2291
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2292 | h2292
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2293 | h2293
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2294 | h2294
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2295 | h2295
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2296 | h2296
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2297 | h2297
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2298 | h2298
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2299 | h2299
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2300 | h2300
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2301 | h2301
                          · linarith only [h1701, h2289, h2293, h2301, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h2301, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1701, h2300, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1593, h1700, h1701, h2289, h2291, h2295, h2299, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h2298, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h2297, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1701, h2289, h2291, h2293, h2296, hlam]
              · linarith only [h1593, h1700, h1701, h2289, h2293, h2295, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · linarith only [h1701, h2289, h2293, h2294, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2311 | h2311
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2312 | h2312
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2313 | h2313
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2314 | h2314
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2315 | h2315
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2316 | h2316
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2317 | h2317
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2318 | h2318
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2319 | h2319
                            · rcases h1bigk with h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [hlam, p2320_0]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h0, hlam, p2320_0]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h1403, hlam, p2320_0]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h1593, hlam, p2320_0]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h1593, h2293, h2311, h2312, h2317, h2319, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2320_1]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h2293, hc01, hc23, hlam, hphi, ht12, p2320_1]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [hlam, p2320_0]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h2293, hlam, p2320_0]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h1593, h2293, hc01, hc23, hlam, hphi, ht12, p2320_1]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                rcases p2320_3 (m.d 0 1) (by simp) with h2330 | h2330
                                · linarith only [h0, h2330, hlam]
                                · linarith only [h1700, h2330, hlam]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                rcases p2320_3 (m.d 0 1) (by simp) with h2333 | h2333
                                · linarith only [h2333, hlam, p2320_0]
                                · rcases p2320_3 (m.d 1 2) (by simp) with h2335 | h2335
                                  · linarith only [h2293, h2335, hlam]
                                  · linarith only [h0, h2335, hlam]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h0, h1700, h2293, h2312, h2317, h2319, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2320_1]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [hlam, p2320_0]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h1593, h1700, h2293, h2312, h2317, h2319, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2320_1]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                rcases p2320_3 (m.d 0 1) (by simp) with h2341 | h2341
                                · linarith only [h1403, h2341, hlam]
                                · linarith only [h1700, h2341, hlam]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h1700, h2293, h2311, h2312, h2317, h2319, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2320_1]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h2311, hlam, p2320_1]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h2313, hlam, p2320_0]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [hlam, p2320_0]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                rcases p2320_3 (m.d 0 1) (by simp) with h2348 | h2348
                                · linarith only [h1593, h2348, hlam]
                                · linarith only [h1700, h2348, hlam]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h1700, hlam, p2320_0]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h2312, hlam, p2320_1]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h2314, hlam, p2320_0]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [h2315, hlam, p2320_0]
                              · have p2320_0 := h2320c.1
                                have p2320_1 := h2320c.2.1
                                have p2320_2 := h2320c.2.2.1
                                have p2320_3 := h2320c.2.2.2
                                linarith only [hlam, p2320_0]
                            · linarith only [h2319, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h2315, h2318, hc24, hlam, hphi, ht45, u5elo1]
                        · linarith only [h1593, h2293, h2311, h2317, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1593, h1700, h2293, h2311, h2315, h2316, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1593, h2315, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1403, h2314, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1403, h1593, h1700, h2291, h2293, h2311, h2312, h2313, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h2312, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h1700, h2289, h2311, hc02, hc15, hlam, hphi, ht0b, ht5b]
        · linarith only [h2292, hc03, hlam, hphi, ht34, ht45, u5elo3]
      · linarith only [h1701, h2289, h2291, hlam]
    · linarith only [h2290, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2368 | h2368
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2369 | h2369
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2370 | h2370
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2371 | h2371
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2372 | h2372
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2373 | h2373
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2374 | h2374
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2375 | h2375
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2376 | h2376
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2377 | h2377
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2378 | h2378
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2379 | h2379
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2380 | h2380
                            · rcases h1bigk with h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c | h2381c
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [hlam, p2381_0]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h0, hlam, p2381_0]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h1403, hlam, p2381_0]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h1593, hlam, p2381_0]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h0, h1701, h2371, h2373, h2378, h2380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2381_1]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                rcases p2381_3 (m.d 0 1) (by simp) with h2387 | h2387
                                · linarith only [h2387, hlam, p2381_0]
                                · rcases p2381_3 (m.d 1 2) (by simp) with h2389 | h2389
                                  · rcases p2381_3 (m.d 1 3) (by simp) with h2390 | h2390
                                    · linarith only [h2371, h2390, hlam]
                                    · linarith only [h1403, h2390, hlam]
                                  · linarith only [h2389, hlam, p2381_0]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [hlam, p2381_0]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h1403, hc01, hc12, hlam, hphi, p2381_1]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h0, h1700, h2289, h2372, h2373, h2378, h2380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2381_1]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h0, h1700, h1701, h2371, hlam, p2381_2]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                rcases p2381_3 (m.d 0 1) (by simp) with h2398 | h2398
                                · linarith only [h2398, hlam, p2381_0]
                                · rcases p2381_3 (m.d 1 2) (by simp) with h2400 | h2400
                                  · rcases p2381_3 (m.d 1 3) (by simp) with h2401 | h2401
                                    · rcases p2381_3 (m.d 1 4) (by simp) with h2402 | h2402
                                      · linarith only [h2374, h2402, hlam]
                                      · linarith only [h1593, h2402, hlam]
                                    · linarith only [h2401, hlam, p2381_0]
                                  · linarith only [h0, h2400, hlam]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h2371, hlam, p2381_1]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [hlam, p2381_0]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h0, h1700, h2289, h2372, h2373, h2378, h2380, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2381_1]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                rcases p2381_3 (m.d 0 1) (by simp) with h2410 | h2410
                                · linarith only [h1403, h2410, hlam]
                                · linarith only [h1700, h2410, hlam]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                rcases p2381_3 (m.d 0 1) (by simp) with h2413 | h2413
                                · linarith only [h2413, hlam, p2381_0]
                                · rcases p2381_3 (m.d 1 2) (by simp) with h2415 | h2415
                                  · rcases p2381_3 (m.d 1 3) (by simp) with h2416 | h2416
                                    · rcases p2381_3 (m.d 1 4) (by simp) with h2417 | h2417
                                      · rcases p2381_3 (m.d 1 5) (by simp) with h2418 | h2418
                                        · linarith only [h2376, h2418, hlam]
                                        · rcases h3bigk with h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h1403, hlam, p2420_1]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h1701, hlam, p2420_1]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h1701, h2371, h2380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2420_1]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            rcases p2420_3 (m.d 0 3) (by simp) with h2425 | h2425
                                            · rcases p2420_3 (m.d 1 3) (by simp) with h2426 | h2426
                                              · rcases p2420_3 (m.d 2 3) (by simp) with h2427 | h2427
                                                · rcases p2420_3 (m.d 3 4) (by simp) with h2428 | h2428
                                                  · linarith only [h2369, h2428, hlam]
                                                  · linarith only [h2380, h2428, hlam]
                                                · linarith only [h2378, h2427, hlam]
                                              · linarith only [h2375, h2426, hlam]
                                            · linarith only [h2425, hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h2369, h2380, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2420_1]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h0, h1700, h1701, h2371, h2373, h2378, h2380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2420_1]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            rcases p2420_3 (m.d 0 3) (by simp) with h2437 | h2437
                                            · linarith only [h1403, h2437, hlam]
                                            · linarith only [h2369, h2437, hlam]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h1700, h2373, h2374, h2378, hlam, p2381_1, p2420_2]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h2369, h2380, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2420_1]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h2371, hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h2371, h2380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2420_1]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            rcases p2420_3 (m.d 0 3) (by simp) with h2445 | h2445
                                            · linarith only [h1701, h2445, hlam]
                                            · linarith only [h2370, h2445, hlam]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h2369, hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h2374, hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h2377, hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h1701, h2369, h2371, h2380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2420_1]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h2370, hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h2375, hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h2378, hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [h2380, hlam, p2420_0]
                                          · have p2420_0 := h2420c.1
                                            have p2420_1 := h2420c.2.1
                                            have p2420_2 := h2420c.2.2.1
                                            have p2420_3 := h2420c.2.2.2
                                            linarith only [hlam, p2420_0]
                                      · linarith only [h2417, hlam, p2381_0]
                                    · linarith only [h1403, h2416, hlam]
                                  · linarith only [h0, h2415, hlam]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h2372, hlam, p2381_1]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h2374, hlam, p2381_0]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [hlam, p2381_0]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                rcases p2381_3 (m.d 0 1) (by simp) with h2464 | h2464
                                · linarith only [h1593, h2464, hlam]
                                · linarith only [h1700, h2464, hlam]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h1700, hlam, p2381_0]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h2373, hlam, p2381_1]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h2375, hlam, p2381_0]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [h2376, hlam, p2381_0]
                              · have p2381_0 := h2381c.1
                                have p2381_1 := h2381c.2.1
                                have p2381_2 := h2381c.2.2.1
                                have p2381_3 := h2381c.2.2.2
                                linarith only [hlam, p2381_0]
                            · linarith only [h2380, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1700, h2289, h2376, h2379, hlam]
                        · linarith only [h0, h2289, h2377, h2378, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1701, h2369, h2377, hlam]
                    · linarith only [h2376, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h2375, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1701, h2369, h2371, h2374, hlam]
              · linarith only [h2373, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h1701, h2371, h2372, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2481 | h2481
            · linarith only [h0, h1700, h2289, h2371, h2481, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2483 | h2483
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2484 | h2484
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2485 | h2485
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2486 | h2486
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2487 | h2487
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2488 | h2488
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2489 | h2489
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2490 | h2490
                            · rcases h1bigk with h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c | h2491c
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h0, hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h1403, hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h1593, hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h0, h2481, h2483, h2487, h2488, h2490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2491_1]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h2481, h2487, hc01, hc23, hlam, hphi, ht12, p2491_1]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h2371, hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h2481, hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                rcases p2491_3 (m.d 0 1) (by simp) with h2501 | h2501
                                · linarith only [h0, h2501, hlam]
                                · linarith only [h1700, h2501, hlam]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                rcases p2491_3 (m.d 0 1) (by simp) with h2504 | h2504
                                · linarith only [h2504, hlam, p2491_0]
                                · rcases p2491_3 (m.d 1 2) (by simp) with h2506 | h2506
                                  · linarith only [h2371, h2506, hlam]
                                  · linarith only [h0, h2506, hlam]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h0, h1700, h2371, h2483, h2488, h2490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2491_1]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h0, h1700, h2371, h2481, h2483, h2488, h2490, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2491_1]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                rcases p2491_3 (m.d 0 1) (by simp) with h2512 | h2512
                                · linarith only [h1403, h2512, hlam]
                                · linarith only [h1700, h2512, hlam]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                rcases p2491_3 (m.d 0 1) (by simp) with h2515 | h2515
                                · linarith only [h2515, hlam, p2491_0]
                                · rcases p2491_3 (m.d 1 2) (by simp) with h2517 | h2517
                                  · linarith only [h2481, h2517, hlam]
                                  · linarith only [h0, h2517, hlam]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h0, h1700, h2483, h2484, h2488, h2490, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2491_1]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h2484, hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                rcases p2491_3 (m.d 0 1) (by simp) with h2523 | h2523
                                · linarith only [h1593, h2523, hlam]
                                · linarith only [h1700, h2523, hlam]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h1700, hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h2483, hlam, p2491_1]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h2485, hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [h2486, hlam, p2491_0]
                              · have p2491_0 := h2491c.1
                                have p2491_1 := h2491c.2.1
                                have p2491_2 := h2491c.2.2.1
                                have p2491_3 := h2491c.2.2.2
                                linarith only [hlam, p2491_0]
                            · linarith only [h2490, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1700, h2481, h2486, h2489, hlam]
                        · linarith only [h0, h2481, h2487, h2488, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h2371, h2487, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h1700, h2481, h2483, h2486, hc25, hlam, hphi, u5elo4]
                  · linarith only [h0, h1700, h2481, h2483, h2484, h2485, hc25, hlam, hphi, u5elo3]
                · linarith only [h1403, h2369, h2484, hlam]
              · linarith only [h0, h2483, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h2289, h2369, h2370, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2540 | h2540
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2541 | h2541
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2542 | h2542
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2543 | h2543
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2544 | h2544
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2545 | h2545
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2546 | h2546
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2547 | h2547
                      · linarith only [h0, h1700, h1701, h2369, h2541, h2543, h2547, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h1700, h1701, h2543, h2544, h2547, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h2546, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h2545, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2552 | h2552
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2553 | h2553
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2554 | h2554
                      · linarith only [h2541, h2544, h2554, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2556 | h2556
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2557 | h2557
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2558 | h2558
                            · rcases h1bigk with h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c | h2559c
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [hlam, p2559_0]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h0, hlam, p2559_0]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h1403, hlam, p2559_0]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h1593, hlam, p2559_0]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h0, h1701, h2541, h2543, h2544, h2556, h2558, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2559_1]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                rcases p2559_3 (m.d 0 1) (by simp) with h2565 | h2565
                                · linarith only [h2565, hlam, p2559_0]
                                · rcases p2559_3 (m.d 1 2) (by simp) with h2567 | h2567
                                  · rcases p2559_3 (m.d 1 3) (by simp) with h2568 | h2568
                                    · linarith only [h2541, h2568, hlam]
                                    · linarith only [h1403, h2568, hlam]
                                  · linarith only [h2567, hlam, p2559_0]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [hlam, p2559_0]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h0, h1701, h2541, hc01, hc12, hlam, hphi, p2559_1]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h1593, h1700, h2543, h2556, h2558, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2559_1]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h0, h1700, h1701, h2541, hlam, p2559_2]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h1700, h2543, h2544, h2556, h2558, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2559_1]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h2541, hlam, p2559_1]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [hlam, p2559_0]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h2544, hlam, p2559_1]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                rcases p2559_3 (m.d 0 1) (by simp) with h2580 | h2580
                                · linarith only [h1403, h2580, hlam]
                                · linarith only [h1700, h2580, hlam]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                rcases p2559_3 (m.d 0 1) (by simp) with h2583 | h2583
                                · linarith only [h2583, hlam, p2559_0]
                                · rcases p2559_3 (m.d 1 2) (by simp) with h2585 | h2585
                                  · rcases p2559_3 (m.d 1 3) (by simp) with h2586 | h2586
                                    · linarith only [h2544, h2586, hlam]
                                    · linarith only [h1403, h2586, hlam]
                                  · linarith only [h0, h2585, hlam]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h2542, hlam, p2559_1]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h1403, h1700, h2543, h2556, h2558, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2559_1]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [hlam, p2559_0]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                rcases p2559_3 (m.d 0 1) (by simp) with h2593 | h2593
                                · linarith only [h1593, h2593, hlam]
                                · linarith only [h1700, h2593, hlam]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h1700, hlam, p2559_0]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h2543, hlam, p2559_1]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h2552, hlam, p2559_0]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [h2553, hlam, p2559_0]
                              · have p2559_0 := h2559c.1
                                have p2559_1 := h2559c.2.1
                                have p2559_2 := h2559c.2.2.1
                                have p2559_3 := h2559c.2.2.2
                                linarith only [hlam, p2559_0]
                            · linarith only [h2558, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1700, h1701, h2553, h2554, h2557, hlam]
                        · linarith only [h0, h1701, h2556, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h2553, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h0, h1700, h1701, h2541, h2543, h2552, hc25, hlam, hphi, u5elo3]
              · linarith only [h2543, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h1700, h1701, h2541, h2542, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2608 | h2608
            · linarith only [h0, h1700, h2289, h2541, h2608, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2610 | h2610
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2611 | h2611
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2612 | h2612
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2613 | h2613
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2614 | h2614
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2615 | h2615
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2616 | h2616
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2617 | h2617
                            · rcases h1bigk with h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c | h2618c
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h0, hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h1403, hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h1593, hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h0, h1701, h2369, h2610, h2611, h2615, h2617, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2618_1]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h2608, h2614, hc01, hc23, hlam, hphi, ht12, p2618_1]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h2541, hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h2608, hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                rcases p2618_3 (m.d 0 1) (by simp) with h2628 | h2628
                                · linarith only [h0, h2628, hlam]
                                · linarith only [h1700, h2628, hlam]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                rcases p2618_3 (m.d 0 1) (by simp) with h2631 | h2631
                                · linarith only [h2631, hlam, p2618_0]
                                · rcases p2618_3 (m.d 1 2) (by simp) with h2633 | h2633
                                  · linarith only [h2541, h2633, hlam]
                                  · linarith only [h0, h2633, hlam]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h0, h1700, h2541, h2610, h2615, h2617, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2618_1]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h0, h1700, h2541, h2608, h2610, h2615, h2617, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2618_1]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h0, h1700, h1701, h2369, h2611, hlam, p2618_2]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                rcases p2618_3 (m.d 0 1) (by simp) with h2640 | h2640
                                · linarith only [h2640, hlam, p2618_0]
                                · rcases p2618_3 (m.d 1 2) (by simp) with h2642 | h2642
                                  · linarith only [h2608, h2642, hlam]
                                  · linarith only [h0, h2642, hlam]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p2618_1]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h2611, hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                rcases p2618_3 (m.d 0 1) (by simp) with h2648 | h2648
                                · linarith only [h1593, h2648, hlam]
                                · linarith only [h1700, h2648, hlam]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h1700, hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h2610, hlam, p2618_1]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h2612, hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [h2613, hlam, p2618_0]
                              · have p2618_0 := h2618c.1
                                have p2618_1 := h2618c.2.1
                                have p2618_2 := h2618c.2.2.1
                                have p2618_3 := h2618c.2.2.2
                                linarith only [hlam, p2618_0]
                            · linarith only [h1701, h2369, h2617, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h0, h1700, h1701, h2369, h2608, h2613, h2616, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1701, h2369, h2541, h2611, h2615, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h2541, h2611, h2614, hlam]
                    · linarith only [h2613, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h0, h1701, h2369, h2611, h2612, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2662 | h2662
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2663 | h2663
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2664 | h2664
                      · linarith only [h1403, h1700, h2610, h2611, h2664, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1700, h2541, h2610, h2664, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h1700, h2541, h2610, h2611, h2663, hc25, hlam, hphi, u5elo4]
                  · linarith only [h0, h1700, h2541, h2610, h2662, hc25, hlam, hphi, u5elo3]
              · linarith only [h0, h2610, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h1700, h1701, h2540, hc15, hlam, hphi, u5elo3]
    · linarith only [h0, h1700, h2368, hc15, hlam, hphi, u5elo2]

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1403 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1593 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1700 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1701 | h1701
  · exact r1l7_11_13_25_L_I_L_I_H_L_x1_x1_x1_x0_x0 m hb1 hb3 hb5 h0 h1403 h1593 h1700 h1701
  · exact r1l7_11_13_25_L_I_L_I_H_L_x1_x1_x1_x0_x1 m hb1 hb3 hb5 h0 h1403 h1593 h1700 h1701

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1403 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1593 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1700 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [h1700, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1403 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1593 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1700 | h1700
  · exact r1l7_11_13_25_L_I_L_I_H_L_x1_x1_x1_x0 m hb1 hb3 hb5 h0 h1403 h1593 h1700
  · exact r1l7_11_13_25_L_I_L_I_H_L_x1_x1_x1_x1 m hb1 hb3 hb5 h0 h1403 h1593 h1700

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1403 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1593 | h1593
  · exact r1l7_11_13_25_L_I_L_I_H_L_x1_x1_x0 m hb1 hb3 hb5 h0 h1403 h1593
  · exact r1l7_11_13_25_L_I_L_I_H_L_x1_x1_x1 m hb1 hb3 hb5 h0 h1403 h1593

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1403 | h1403
  · exact r1l7_11_13_25_L_I_L_I_H_L_x1_x0 m hb1 hb3 hb5 h0 h1403
  · exact r1l7_11_13_25_L_I_L_I_H_L_x1_x1 m hb1 hb3 hb5 h0 h1403

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_I_L_I_H_L_x0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_I_L_I_H_L_x1 m hb1 hb3 hb5 h0

end R2N4
