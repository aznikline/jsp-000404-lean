import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1732 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2007 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2155 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2349 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h2350 | h2350
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2351 | h2351
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2352 | h2352
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2353 | h2353
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2354 | h2354
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2355 | h2355
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2356 | h2356
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2357 | h2357
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2358 | h2358
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2359 | h2359
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2360 | h2360
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2361 | h2361
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2362 | h2362
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2363 | h2363
                            · linarith only [h2349, h2360, h2363, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                            · rcases h1bigk with h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [hlam, p2365_0]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h0, hlam, p2365_0]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h1732, hlam, p2365_0]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2007, hlam, p2365_0]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2155, hlam, p2365_0]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                rcases p2365_3 (m.d 0 1) (by simp) with h2371 | h2371
                                · linarith only [h2371, hlam, p2365_0]
                                · rcases p2365_3 (m.d 1 2) (by simp) with h2373 | h2373
                                  · rcases p2365_3 (m.d 1 3) (by simp) with h2374 | h2374
                                    · linarith only [h2354, h2374, hlam]
                                    · linarith only [h1732, h2374, hlam]
                                  · linarith only [h2373, hlam, p2365_0]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [hlam, p2365_0]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h1732, hc01, hc12, hlam, hphi, p2365_1]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2007, h2353, h2363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2365_1]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2155, hc01, hc12, hlam, hphi, p2365_1]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                rcases p2365_3 (m.d 0 1) (by simp) with h2382 | h2382
                                · linarith only [h2382, hlam, p2365_0]
                                · rcases p2365_3 (m.d 1 2) (by simp) with h2384 | h2384
                                  · rcases p2365_3 (m.d 1 3) (by simp) with h2385 | h2385
                                    · rcases p2365_3 (m.d 1 4) (by simp) with h2386 | h2386
                                      · linarith only [h2357, h2386, hlam]
                                      · linarith only [h2007, h2386, hlam]
                                    · linarith only [h2385, hlam, p2365_0]
                                  · linarith only [h0, h2384, hlam]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2354, hlam, p2365_1]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [hlam, p2365_0]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2007, h2353, h2363, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2365_1]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2155, h2354, hc01, hc12, hlam, hphi, p2365_1]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                rcases p2365_3 (m.d 0 1) (by simp) with h2395 | h2395
                                · linarith only [h2395, hlam, p2365_0]
                                · rcases p2365_3 (m.d 1 2) (by simp) with h2397 | h2397
                                  · rcases p2365_3 (m.d 1 3) (by simp) with h2398 | h2398
                                    · rcases p2365_3 (m.d 1 4) (by simp) with h2399 | h2399
                                      · rcases p2365_3 (m.d 1 5) (by simp) with h2400 | h2400
                                        · linarith only [h2359, h2400, hlam]
                                        · linarith only [h2155, h2400, hlam]
                                      · linarith only [h2399, hlam, p2365_0]
                                    · linarith only [h1732, h2398, hlam]
                                  · linarith only [h0, h2397, hlam]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2355, hlam, p2365_1]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2357, hlam, p2365_0]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [hlam, p2365_0]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2155, hc01, hc14, hlam, hphi, p2365_1]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2365_1, u5elo1]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2356, hlam, p2365_1]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2358, hlam, p2365_0]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [h2359, hlam, p2365_0]
                              · have p2365_0 := h2365c.1
                                have p2365_1 := h2365c.2.1
                                have p2365_2 := h2365c.2.2.1
                                have p2365_3 := h2365c.2.2.2
                                linarith only [hlam, p2365_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2415 | h2415
                            · linarith only [h2360, h2362, h2415, hlam]
                            · rcases h1bigk with h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [hlam, p2417_0]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h0, hlam, p2417_0]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h1732, hlam, p2417_0]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2007, hlam, p2417_0]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2155, hlam, p2417_0]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                rcases p2417_3 (m.d 0 1) (by simp) with h2423 | h2423
                                · linarith only [h2423, hlam, p2417_0]
                                · rcases p2417_3 (m.d 1 2) (by simp) with h2425 | h2425
                                  · rcases p2417_3 (m.d 1 3) (by simp) with h2426 | h2426
                                    · linarith only [h2354, h2426, hlam]
                                    · linarith only [h1732, h2426, hlam]
                                  · linarith only [h2425, hlam, p2417_0]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [hlam, p2417_0]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h1732, hc01, hc12, hlam, hphi, p2417_1]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2007, hc01, hc12, hlam, hphi, p2417_1]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2155, hc01, hc12, hlam, hphi, p2417_1]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                rcases p2417_3 (m.d 0 1) (by simp) with h2434 | h2434
                                · linarith only [h2434, hlam, p2417_0]
                                · rcases p2417_3 (m.d 1 2) (by simp) with h2436 | h2436
                                  · rcases p2417_3 (m.d 1 3) (by simp) with h2437 | h2437
                                    · rcases p2417_3 (m.d 1 4) (by simp) with h2438 | h2438
                                      · linarith only [h2357, h2438, hlam]
                                      · linarith only [h2007, h2438, hlam]
                                    · linarith only [h2437, hlam, p2417_0]
                                  · linarith only [h0, h2436, hlam]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2354, hlam, p2417_1]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [hlam, p2417_0]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2007, h2353, h2360, h2362, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2417_1]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2155, h2354, hc01, hc12, hlam, hphi, p2417_1]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                rcases p2417_3 (m.d 0 1) (by simp) with h2447 | h2447
                                · linarith only [h2447, hlam, p2417_0]
                                · rcases p2417_3 (m.d 1 2) (by simp) with h2449 | h2449
                                  · rcases p2417_3 (m.d 1 3) (by simp) with h2450 | h2450
                                    · rcases p2417_3 (m.d 1 4) (by simp) with h2451 | h2451
                                      · rcases p2417_3 (m.d 1 5) (by simp) with h2452 | h2452
                                        · linarith only [h2359, h2452, hlam]
                                        · linarith only [h2155, h2452, hlam]
                                      · linarith only [h2451, hlam, p2417_0]
                                    · linarith only [h1732, h2450, hlam]
                                  · linarith only [h0, h2449, hlam]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2355, hlam, p2417_1]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2357, hlam, p2417_0]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [hlam, p2417_0]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2155, hc01, hc14, hlam, hphi, p2417_1]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2417_1, u5elo1]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2356, hlam, p2417_1]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2358, hlam, p2417_0]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [h2359, hlam, p2417_0]
                              · have p2417_0 := h2417c.1
                                have p2417_1 := h2417c.2.1
                                have p2417_2 := h2417c.2.2.1
                                have p2417_3 := h2417c.2.2.2
                                linarith only [hlam, p2417_0]
                        · linarith only [h2155, h2352, h2360, h2361, hc34, hlam, hphi, ht45, u5elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2468 | h2468
                        · linarith only [h2351, h2360, h2468, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2470 | h2470
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2471 | h2471
                            · rcases h1bigk with h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c | h2472c
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [hlam, p2472_0]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h0, hlam, p2472_0]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h1732, hlam, p2472_0]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2007, hlam, p2472_0]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2155, hlam, p2472_0]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                rcases p2472_3 (m.d 0 1) (by simp) with h2478 | h2478
                                · linarith only [h2478, hlam, p2472_0]
                                · rcases p2472_3 (m.d 1 2) (by simp) with h2480 | h2480
                                  · rcases p2472_3 (m.d 1 3) (by simp) with h2481 | h2481
                                    · linarith only [h2354, h2481, hlam]
                                    · linarith only [h1732, h2481, hlam]
                                  · linarith only [h2480, hlam, p2472_0]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [hlam, p2472_0]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h1732, h2351, h2360, h2470, hc12, hlam, hphi, ht01, ht0b, ht5b, p2472_1, u5ehi9]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2007, hc01, hc12, hlam, hphi, p2472_1]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2155, hc01, hc12, hlam, hphi, p2472_1]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                rcases p2472_3 (m.d 0 1) (by simp) with h2489 | h2489
                                · linarith only [h2489, hlam, p2472_0]
                                · rcases p2472_3 (m.d 1 2) (by simp) with h2491 | h2491
                                  · rcases p2472_3 (m.d 1 3) (by simp) with h2492 | h2492
                                    · rcases p2472_3 (m.d 1 4) (by simp) with h2493 | h2493
                                      · linarith only [h2357, h2493, hlam]
                                      · linarith only [h2007, h2493, hlam]
                                    · linarith only [h2492, hlam, p2472_0]
                                  · linarith only [h0, h2491, hlam]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2354, hlam, p2472_1]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [hlam, p2472_0]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2007, h2351, h2360, h2470, hc13, hlam, hphi, ht01, ht0b, ht5b, p2472_1, u5ehi9]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2155, h2354, hc01, hc12, hlam, hphi, p2472_1]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                rcases p2472_3 (m.d 0 1) (by simp) with h2502 | h2502
                                · linarith only [h2502, hlam, p2472_0]
                                · rcases p2472_3 (m.d 1 2) (by simp) with h2504 | h2504
                                  · rcases p2472_3 (m.d 1 3) (by simp) with h2505 | h2505
                                    · rcases p2472_3 (m.d 1 4) (by simp) with h2506 | h2506
                                      · rcases p2472_3 (m.d 1 5) (by simp) with h2507 | h2507
                                        · linarith only [h2359, h2507, hlam]
                                        · linarith only [h2155, h2507, hlam]
                                      · linarith only [h2506, hlam, p2472_0]
                                    · linarith only [h1732, h2505, hlam]
                                  · linarith only [h0, h2504, hlam]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2355, hlam, p2472_1]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2357, hlam, p2472_0]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [hlam, p2472_0]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2155, hc01, hc14, hlam, hphi, p2472_1]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2472_1, u5elo1]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2356, hlam, p2472_1]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2358, hlam, p2472_0]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [h2359, hlam, p2472_0]
                              · have p2472_0 := h2472c.1
                                have p2472_1 := h2472c.2.1
                                have p2472_2 := h2472c.2.2.1
                                have p2472_3 := h2472c.2.2.2
                                linarith only [hlam, p2472_0]
                            · linarith only [h2360, h2470, h2471, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2523 | h2523
                            · rcases h1bigk with h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c | h2524c
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [hlam, p2524_0]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h0, hlam, p2524_0]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h1732, hlam, p2524_0]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2007, hlam, p2524_0]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2155, hlam, p2524_0]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                rcases p2524_3 (m.d 0 1) (by simp) with h2530 | h2530
                                · linarith only [h2530, hlam, p2524_0]
                                · rcases p2524_3 (m.d 1 2) (by simp) with h2532 | h2532
                                  · rcases p2524_3 (m.d 1 3) (by simp) with h2533 | h2533
                                    · linarith only [h2354, h2533, hlam]
                                    · linarith only [h1732, h2533, hlam]
                                  · linarith only [h2532, hlam, p2524_0]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [hlam, p2524_0]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h1732, h2351, h2360, h2470, h2523, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2524_1]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2007, hc01, hc12, hlam, hphi, p2524_1]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2155, hc01, hc12, hlam, hphi, p2524_1]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                rcases p2524_3 (m.d 0 1) (by simp) with h2541 | h2541
                                · linarith only [h2541, hlam, p2524_0]
                                · rcases p2524_3 (m.d 1 2) (by simp) with h2543 | h2543
                                  · rcases p2524_3 (m.d 1 3) (by simp) with h2544 | h2544
                                    · rcases p2524_3 (m.d 1 4) (by simp) with h2545 | h2545
                                      · linarith only [h2357, h2545, hlam]
                                      · linarith only [h2007, h2545, hlam]
                                    · linarith only [h2544, hlam, p2524_0]
                                  · linarith only [h0, h2543, hlam]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2354, hlam, p2524_1]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [hlam, p2524_0]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2007, h2351, h2360, h2470, h2523, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2524_1]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2155, h2354, hc01, hc12, hlam, hphi, p2524_1]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                rcases p2524_3 (m.d 0 1) (by simp) with h2554 | h2554
                                · linarith only [h2554, hlam, p2524_0]
                                · rcases p2524_3 (m.d 1 2) (by simp) with h2556 | h2556
                                  · rcases p2524_3 (m.d 1 3) (by simp) with h2557 | h2557
                                    · rcases p2524_3 (m.d 1 4) (by simp) with h2558 | h2558
                                      · rcases p2524_3 (m.d 1 5) (by simp) with h2559 | h2559
                                        · linarith only [h2359, h2559, hlam]
                                        · linarith only [h2155, h2559, hlam]
                                      · linarith only [h2558, hlam, p2524_0]
                                    · linarith only [h1732, h2557, hlam]
                                  · linarith only [h0, h2556, hlam]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2355, hlam, p2524_1]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2357, hlam, p2524_0]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [hlam, p2524_0]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2155, hc01, hc14, hlam, hphi, p2524_1]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2524_1, u5elo1]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2356, hlam, p2524_1]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2358, hlam, p2524_0]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [h2359, hlam, p2524_0]
                              · have p2524_0 := h2524c.1
                                have p2524_1 := h2524c.2.1
                                have p2524_2 := h2524c.2.2.1
                                have p2524_3 := h2524c.2.2.2
                                linarith only [hlam, p2524_0]
                            · linarith only [h2360, h2523, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h2007, h2155, h2353, h2359, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h1732, h2155, h2352, h2358, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                · linarith only [h1732, h2351, h2357, hlam]
              · linarith only [h0, h2356, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2579 | h2579
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2580 | h2580
                · linarith only [h2354, h2355, h2580, hlam]
                · linarith only [h0, h1732, h2349, h2351, h2355, h2580, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h2350, h2579, hlam]
          · linarith only [h0, h2349, h2354, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2585 | h2585
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2586 | h2586
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2587 | h2587
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2588 | h2588
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2589 | h2589
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2590 | h2590
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2591 | h2591
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2592 | h2592
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2593 | h2593
                          · linarith only [h0, h2007, h2349, h2353, h2591, h2593, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2595 | h2595
                            · linarith only [h2351, h2353, h2595, hlam]
                            · rcases h1bigk with h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c
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
                                linarith only [h1732, hlam, p2597_0]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2007, hlam, p2597_0]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2155, hlam, p2597_0]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                rcases p2597_3 (m.d 0 1) (by simp) with h2603 | h2603
                                · linarith only [h2603, hlam, p2597_0]
                                · rcases p2597_3 (m.d 1 2) (by simp) with h2605 | h2605
                                  · rcases p2597_3 (m.d 1 3) (by simp) with h2606 | h2606
                                    · linarith only [h2585, h2606, hlam]
                                    · linarith only [h1732, h2606, hlam]
                                  · linarith only [h2605, hlam, p2597_0]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [hlam, p2597_0]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2007, h2353, h2588, h2590, hc01, hc12, hlam, hphi, p2597_1]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2007, h2353, h2590, hc01, hc12, hlam, hphi, p2597_1]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2007, h2353, h2590, hc01, hc12, hlam, hphi, p2597_1]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                rcases p2597_3 (m.d 0 1) (by simp) with h2614 | h2614
                                · linarith only [h2614, hlam, p2597_0]
                                · rcases p2597_3 (m.d 1 2) (by simp) with h2616 | h2616
                                  · rcases p2597_3 (m.d 1 3) (by simp) with h2617 | h2617
                                    · rcases p2597_3 (m.d 1 4) (by simp) with h2618 | h2618
                                      · linarith only [h2588, h2618, hlam]
                                      · linarith only [h2007, h2618, hlam]
                                    · linarith only [h2617, hlam, p2597_0]
                                  · linarith only [h0, h2616, hlam]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2585, hlam, p2597_1]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [hlam, p2597_0]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2007, h2353, h2590, hc01, hc13, hlam, hphi, p2597_1]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2007, h2353, h2585, h2590, hc01, hc12, hlam, hphi, p2597_1]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                rcases p2597_3 (m.d 0 1) (by simp) with h2627 | h2627
                                · linarith only [h2627, hlam, p2597_0]
                                · rcases p2597_3 (m.d 1 2) (by simp) with h2629 | h2629
                                  · rcases p2597_3 (m.d 1 3) (by simp) with h2630 | h2630
                                    · rcases p2597_3 (m.d 1 4) (by simp) with h2631 | h2631
                                      · rcases p2597_3 (m.d 1 5) (by simp) with h2632 | h2632
                                        · linarith only [h2590, h2632, hlam]
                                        · linarith only [h2155, h2632, hlam]
                                      · linarith only [h2631, hlam, p2597_0]
                                    · linarith only [h1732, h2630, hlam]
                                  · linarith only [h0, h2629, hlam]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2586, hlam, p2597_1]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2588, hlam, p2597_0]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [hlam, p2597_0]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2007, h2353, h2590, hc01, hc14, hlam, hphi, p2597_1]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2597_1, u5elo1]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2587, hlam, p2597_1]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2589, hlam, p2597_0]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [h2590, hlam, p2597_0]
                              · have p2597_0 := h2597c.1
                                have p2597_1 := h2597c.2.1
                                have p2597_2 := h2597c.2.2.1
                                have p2597_3 := h2597c.2.2.2
                                linarith only [hlam, p2597_0]
                        · linarith only [h2352, h2353, h2590, h2591, h2592, hc34, hlam, hphi, ht45, u5elo1]
                      · linarith only [h2351, h2353, h2590, h2591, hc23, hlam, hphi, ht34, ht45, u5elo1]
                    · linarith only [h2007, h2590, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1732, h2155, h2352, h2589, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                · linarith only [h1732, h2351, h2353, h2588, hc03, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h0, h2587, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2653 | h2653
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2654 | h2654
                · linarith only [h2585, h2586, h2654, hlam]
                · linarith only [h0, h1732, h2349, h2351, h2586, h2654, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h2349, h2352, h2653, hlam, hphi, u5ehi8, u5elo2]
          · linarith only [h0, h2349, h2585, hlam]
      · linarith only [h2351, h2352, hc34, hlam, hphi, ht45, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2660 | h2660
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2661 | h2661
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2662 | h2662
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2663 | h2663
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2664 | h2664
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2665 | h2665
                · linarith only [h2351, h2660, h2665, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2667 | h2667
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2668 | h2668
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2669 | h2669
                      · linarith only [h1732, h2349, h2665, h2669, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2671 | h2671
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2672 | h2672
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2673 | h2673
                            · rcases h1bigk with h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h0, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h1732, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2007, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2155, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                rcases p2674_3 (m.d 0 1) (by simp) with h2680 | h2680
                                · linarith only [h2680, hlam, p2674_0]
                                · rcases p2674_3 (m.d 1 2) (by simp) with h2682 | h2682
                                  · rcases p2674_3 (m.d 1 3) (by simp) with h2683 | h2683
                                    · linarith only [h2662, h2683, hlam]
                                    · linarith only [h1732, h2683, hlam]
                                  · linarith only [h2682, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h1732, h2349, h2671, h2673, hc12, hlam, hphi, ht01, ht0b, ht5b, p2674_1, u5ehi9]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2007, hc01, hc12, hlam, hphi, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2155, hc01, hc12, hlam, hphi, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2665, hc01, hc34, hlam, hphi, ht12, ht23, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2662, hlam, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2665, hlam, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2155, hc01, hc13, hlam, hphi, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                rcases p2674_3 (m.d 0 1) (by simp) with h2696 | h2696
                                · linarith only [h2696, hlam, p2674_0]
                                · rcases p2674_3 (m.d 1 2) (by simp) with h2698 | h2698
                                  · rcases p2674_3 (m.d 1 3) (by simp) with h2699 | h2699
                                    · linarith only [h2665, h2699, hlam]
                                    · linarith only [h1732, h2699, hlam]
                                  · linarith only [h0, h2698, hlam]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2663, hlam, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h1732, h2665, hc01, hc34, hlam, hphi, ht12, ht23, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2155, h2665, hc01, hc34, hlam, hphi, ht12, ht23, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2674_1, u5elo1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2664, hlam, p2674_1]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2667, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [h2668, hlam, p2674_0]
                              · have p2674_0 := h2674c.1
                                have p2674_1 := h2674c.2.1
                                have p2674_2 := h2674c.2.2.1
                                have p2674_3 := h2674c.2.2.2
                                linarith only [hlam, p2674_0]
                            · linarith only [h1732, h2349, h2665, h2671, h2673, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                          · linarith only [h2155, h2661, h2669, h2671, h2672, hlam, hphi, u5ehi8, u5elo1]
                        · linarith only [h1732, h2660, h2665, h2671, hc23, hc34, hlam, hphi]
                    · linarith only [h2007, h2155, h2661, h2668, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h1732, h2660, h2667, hlam]
              · linarith only [h0, h2155, h2350, h2664, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2718 | h2718
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2719 | h2719
                · linarith only [h2351, h2660, h2719, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2721 | h2721
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2722 | h2722
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2723 | h2723
                      · linarith only [h1732, h2719, h2723, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2725 | h2725
                        · linarith only [h0, h2349, h2663, h2725, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                        · linarith only [h0, h2349, h2660, h2663, h2723, h2725, hc23, hc34, hlam, hphi]
                    · linarith only [h2007, h2661, h2722, hlam]
                  · linarith only [h1732, h2660, h2721, hlam]
              · linarith only [h0, h2350, h2718, hlam]
          · linarith only [h0, h2349, h2662, hlam]
        · linarith only [h2351, h2660, h2661, hlam, hphi, u5ehi8, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2733 | h2733
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2734 | h2734
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2735 | h2735
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2736 | h2736
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2737 | h2737
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2738 | h2738
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2739 | h2739
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2740 | h2740
                      · linarith only [h2349, h2351, h2733, h2740, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2742 | h2742
                        · linarith only [h2349, h2350, h2351, h2660, h2737, h2742, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2744 | h2744
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2745 | h2745
                            · rcases h1bigk with h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c | h2746c
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [hlam, p2746_0]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h0, hlam, p2746_0]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h1732, hlam, p2746_0]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h2007, hlam, p2746_0]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h2155, hlam, p2746_0]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                rcases p2746_3 (m.d 0 1) (by simp) with h2752 | h2752
                                · linarith only [h2752, hlam, p2746_0]
                                · rcases p2746_3 (m.d 1 2) (by simp) with h2754 | h2754
                                  · rcases p2746_3 (m.d 1 3) (by simp) with h2755 | h2755
                                    · linarith only [h2734, h2755, hlam]
                                    · linarith only [h1732, h2755, hlam]
                                  · linarith only [h2754, hlam, p2746_0]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [hlam, p2746_0]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h1732, hc01, hc12, hlam, hphi, p2746_1]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h1732, h2007, h2660, h2733, h2738, hc01, hc12, hlam, hphi, p2746_1, u5ehi9, u5elo1]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h1732, h2660, h2738, hc01, hc12, hlam, hphi, p2746_1]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                rcases p2746_3 (m.d 0 1) (by simp) with h2763 | h2763
                                · linarith only [h2763, hlam, p2746_0]
                                · rcases p2746_3 (m.d 1 2) (by simp) with h2765 | h2765
                                  · rcases p2746_3 (m.d 1 3) (by simp) with h2766 | h2766
                                    · rcases p2746_3 (m.d 1 4) (by simp) with h2767 | h2767
                                      · linarith only [h2737, h2767, hlam]
                                      · linarith only [h2007, h2767, hlam]
                                    · linarith only [h2766, hlam, p2746_0]
                                  · linarith only [h0, h2765, hlam]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h2734, hlam, p2746_1]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [hlam, p2746_0]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h1732, h2351, h2660, h2733, h2737, h2738, hc01, hc13, hlam, hphi, p2746_1, u5ehi9, u5elo1]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h1732, h2660, h2734, h2738, hc01, hc12, hlam, hphi, p2746_1]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                rcases p2746_3 (m.d 0 1) (by simp) with h2776 | h2776
                                · linarith only [h2776, hlam, p2746_0]
                                · rcases p2746_3 (m.d 1 2) (by simp) with h2778 | h2778
                                  · rcases p2746_3 (m.d 1 3) (by simp) with h2779 | h2779
                                    · rcases p2746_3 (m.d 1 4) (by simp) with h2780 | h2780
                                      · rcases p2746_3 (m.d 1 5) (by simp) with h2781 | h2781
                                        · linarith only [h2739, h2781, hlam]
                                        · linarith only [h2155, h2781, hlam]
                                      · linarith only [h2780, hlam, p2746_0]
                                    · linarith only [h1732, h2779, hlam]
                                  · linarith only [h0, h2778, hlam]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h2735, hlam, p2746_1]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h2737, hlam, p2746_0]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [hlam, p2746_0]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h1732, h2660, h2738, hc01, hc14, hlam, hphi, p2746_1]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2746_1, u5elo1]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h2736, hlam, p2746_1]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h2738, hlam, p2746_0]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [h2739, hlam, p2746_0]
                              · have p2746_0 := h2746c.1
                                have p2746_1 := h2746c.2.1
                                have p2746_2 := h2746c.2.2.1
                                have p2746_3 := h2746c.2.2.2
                                linarith only [hlam, p2746_0]
                            · linarith only [h2351, h2733, h2745, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2797 | h2797
                            · rcases h1bigk with h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c | h2798c
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [hlam, p2798_0]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h0, hlam, p2798_0]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h1732, hlam, p2798_0]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h2007, hlam, p2798_0]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h2155, hlam, p2798_0]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                rcases p2798_3 (m.d 0 1) (by simp) with h2804 | h2804
                                · linarith only [h2804, hlam, p2798_0]
                                · rcases p2798_3 (m.d 1 2) (by simp) with h2806 | h2806
                                  · rcases p2798_3 (m.d 1 3) (by simp) with h2807 | h2807
                                    · linarith only [h2734, h2807, hlam]
                                    · linarith only [h1732, h2807, hlam]
                                  · linarith only [h2806, hlam, p2798_0]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [hlam, p2798_0]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h2351, h2733, h2737, h2740, h2744, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2798_1]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h2007, hc01, hc12, hlam, hphi, p2798_1]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h1732, h2660, h2738, hc01, hc12, hlam, hphi, p2798_1]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                rcases p2798_3 (m.d 0 1) (by simp) with h2815 | h2815
                                · linarith only [h2815, hlam, p2798_0]
                                · rcases p2798_3 (m.d 1 2) (by simp) with h2817 | h2817
                                  · rcases p2798_3 (m.d 1 3) (by simp) with h2818 | h2818
                                    · rcases p2798_3 (m.d 1 4) (by simp) with h2819 | h2819
                                      · linarith only [h2737, h2819, hlam]
                                      · linarith only [h2007, h2819, hlam]
                                    · linarith only [h2818, hlam, p2798_0]
                                  · linarith only [h0, h2817, hlam]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h2734, hlam, p2798_1]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [hlam, p2798_0]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h1732, h2351, h2660, h2733, h2737, h2738, h2740, h2744, hc01, hc13, hc23, hlam, hphi, ht34, ht45, p2798_1, u5elo1]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h1732, h2660, h2734, h2738, hc01, hc12, hlam, hphi, p2798_1]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                rcases p2798_3 (m.d 0 1) (by simp) with h2828 | h2828
                                · linarith only [h2828, hlam, p2798_0]
                                · rcases p2798_3 (m.d 1 2) (by simp) with h2830 | h2830
                                  · rcases p2798_3 (m.d 1 3) (by simp) with h2831 | h2831
                                    · rcases p2798_3 (m.d 1 4) (by simp) with h2832 | h2832
                                      · rcases p2798_3 (m.d 1 5) (by simp) with h2833 | h2833
                                        · linarith only [h2739, h2833, hlam]
                                        · linarith only [h2155, h2833, hlam]
                                      · linarith only [h2832, hlam, p2798_0]
                                    · linarith only [h1732, h2831, hlam]
                                  · linarith only [h0, h2830, hlam]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h2735, hlam, p2798_1]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h2737, hlam, p2798_0]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [hlam, p2798_0]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h1732, h2660, h2738, hc01, hc14, hlam, hphi, p2798_1]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2798_1, u5elo1]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h2736, hlam, p2798_1]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h2738, hlam, p2798_0]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [h2739, hlam, p2798_0]
                              · have p2798_0 := h2798c.1
                                have p2798_1 := h2798c.2.1
                                have p2798_2 := h2798c.2.2.1
                                have p2798_3 := h2798c.2.2.2
                                linarith only [hlam, p2798_0]
                            · linarith only [h2351, h2733, h2797, hlam]
                    · linarith only [h2007, h2351, h2733, h2734, h2737, h2739, hc01, hc12, hlam, hphi]
                  · linarith only [h2351, h2733, h2737, h2738, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2851 | h2851
                  · linarith only [h2660, h2737, h2851, hc03, hc34, hlam, hphi]
                  · linarith only [h1732, h2851, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h2007, h2350, h2733, h2735, h2736, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2855 | h2855
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2856 | h2856
                · linarith only [h2351, h2733, h2734, h2735, h2856, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2858 | h2858
                  · linarith only [h1732, h2660, h2734, h2735, h2858, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h1732, h2858, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h2350, h2855, hlam]
          · linarith only [h0, h2349, h2734, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2863 | h2863
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2864 | h2864
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2865 | h2865
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2866 | h2866
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2867 | h2867
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2868 | h2868
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2869 | h2869
                      · linarith only [h2349, h2351, h2869, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2871 | h2871
                        · linarith only [h2349, h2350, h2351, h2660, h2733, h2868, h2871, hlam, hphi, u5ehi7, u5elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2873 | h2873
                          · linarith only [h1732, h2351, h2733, h2864, h2873, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2875 | h2875
                            · linarith only [h1732, h2351, h2733, h2866, h2875, hc01, hc13, hlam, hphi]
                            · linarith only [h1732, h2351, h2868, h2875, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                    · linarith only [h2007, h2868, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1732, h2867, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2880 | h2880
                  · linarith only [h1732, h2660, h2866, h2880, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1732, h2880, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h2350, h2865, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2884 | h2884
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2885 | h2885
                · linarith only [h1732, h2351, h2863, h2864, h2885, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2887 | h2887
                  · linarith only [h1732, h2660, h2863, h2864, h2887, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h1732, h2887, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h2350, h2884, hlam]
          · linarith only [h0, h2349, h2863, hlam]
  · linarith only [h2349, h2350, hc23, hlam, hphi, ht34, ht45, u5elo2]

end R2N4
