import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1750 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2167 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2337 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h2338 | h2338
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2339 | h2339
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2340 | h2340
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2341 | h2341
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2342 | h2342
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2343 | h2343
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2344 | h2344
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2345 | h2345
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2346 | h2346
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2347 | h2347
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2348 | h2348
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2349 | h2349
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2350 | h2350
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2351 | h2351
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2352 | h2352
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2353 | h2353
                                · linarith only [h2338, h2350, h2353, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                                · rcases h2bigk with h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c | h2355c
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [hlam, p2355_0]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h0, hlam, p2355_1]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h0, h2350, h2352, h2353, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2355_1]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h0, h2352, h2353, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2355_1]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    rcases p2355_3 (m.d 0 2) (by simp) with h2360 | h2360
                                    · rcases p2355_3 (m.d 1 2) (by simp) with h2361 | h2361
                                      · rcases p2355_3 (m.d 2 3) (by simp) with h2362 | h2362
                                        · linarith only [h2338, h2362, hlam]
                                        · linarith only [h2351, h2362, hlam]
                                      · linarith only [h2346, h2361, hlam]
                                    · linarith only [h2360, hlam, p2355_0]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h0, h2337, hc12, hlam, hphi, ht01, ht0b, ht5b, p2355_1, u5ehi6]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [hlam, p2355_0]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h2350, h2352, h2353, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2355_1]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h2352, h2353, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2355_1]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    rcases p2355_3 (m.d 0 2) (by simp) with h2371 | h2371
                                    · linarith only [h0, h2371, hlam]
                                    · linarith only [h2340, h2371, hlam]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h2338, hlam, p2355_0]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h2344, hlam, p2355_0]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [hlam, p2355_0]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h2338, h2352, h2353, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2355_1]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h0, h2338, h2352, h2353, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2355_1]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h2339, hlam, p2355_0]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h2345, hlam, p2355_0]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h2350, hlam, p2355_1]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [hlam, p2355_0]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h0, h2339, h2352, h2353, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2355_1]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h2340, hlam, p2355_0]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h2346, hlam, p2355_0]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h2351, hlam, p2355_1]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [h2352, hlam, p2355_0]
                                  · have p2355_0 := h2355c.1
                                    have p2355_1 := h2355c.2.1
                                    have p2355_2 := h2355c.2.2.1
                                    have p2355_3 := h2355c.2.2.2
                                    linarith only [hlam, p2355_0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2389 | h2389
                                · linarith only [h0, h2338, h2350, h2352, h2389, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h2bigk with h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [hlam, p2391_0]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h0, hlam, p2391_1]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h0, h2351, hc12, hlam, hphi, ht01, ht0b, ht5b, p2391_1, u5ehi8]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    rcases p2391_3 (m.d 0 2) (by simp) with h2395 | h2395
                                    · rcases p2391_3 (m.d 1 2) (by simp) with h2396 | h2396
                                      · rcases p2391_3 (m.d 2 3) (by simp) with h2397 | h2397
                                        · linarith only [h2338, h2397, hlam]
                                        · linarith only [h2350, h2397, hlam]
                                      · linarith only [h2345, h2396, hlam]
                                    · linarith only [h2395, hlam, p2391_0]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    rcases p2391_3 (m.d 0 2) (by simp) with h2402 | h2402
                                    · rcases p2391_3 (m.d 1 2) (by simp) with h2403 | h2403
                                      · rcases p2391_3 (m.d 2 3) (by simp) with h2404 | h2404
                                        · linarith only [h2338, h2404, hlam]
                                        · linarith only [h2351, h2404, hlam]
                                      · linarith only [h2346, h2403, hlam]
                                    · linarith only [h2402, hlam, p2391_0]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h0, h2337, hc12, hlam, hphi, ht01, ht0b, ht5b, p2391_1, u5ehi6]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [hlam, p2391_0]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2351, hc12, hlam, hphi, ht01, ht0b, ht5b, p2391_1, u5ehi8]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2167, h2337, h2344, h2347, h2349, h2352, hlam, p2391_2]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    rcases p2391_3 (m.d 0 2) (by simp) with h2413 | h2413
                                    · linarith only [h0, h2413, hlam]
                                    · linarith only [h2340, h2413, hlam]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2338, hlam, p2391_0]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2344, hlam, p2391_0]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [hlam, p2391_0]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    rcases p2391_3 (m.d 0 2) (by simp) with h2419 | h2419
                                    · rcases p2391_3 (m.d 1 2) (by simp) with h2420 | h2420
                                      · rcases p2391_3 (m.d 2 3) (by simp) with h2421 | h2421
                                        · rcases p2391_3 (m.d 2 4) (by simp) with h2422 | h2422
                                          · linarith only [h2350, h2422, hlam]
                                          · rcases p2391_3 (m.d 2 5) (by simp) with h2424 | h2424
                                            · linarith only [h2351, h2424, hlam]
                                            · linarith only [h2352, h2424, hlam]
                                        · linarith only [h2350, h2421, hlam]
                                      · linarith only [h2345, h2420, hlam]
                                    · linarith only [h2339, h2419, hlam]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2338, h2351, hc02, hlam, hphi, ht0b, ht5b, p2391_1, u5ehi8]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2339, hlam, p2391_0]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2345, hlam, p2391_0]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2350, hlam, p2391_1]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [hlam, p2391_0]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2352, hlam, p2391_1]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2340, hlam, p2391_0]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2346, hlam, p2391_0]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2351, hlam, p2391_1]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [h2350, hc34, hlam, hphi, ht45, p2391_1, u5elo2]
                                  · have p2391_0 := h2391c.1
                                    have p2391_1 := h2391c.2.1
                                    have p2391_2 := h2391c.2.2.1
                                    have p2391_3 := h2391c.2.2.2
                                    linarith only [hlam, p2391_0]
                            · linarith only [h2167, h2337, h2347, h2348, h2350, h2351, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2442 | h2442
                            · linarith only [h2341, h2350, h2442, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2444 | h2444
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2445 | h2445
                                · rcases h2bigk with h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h0, hlam, p2446_1]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    rcases p2446_3 (m.d 0 2) (by simp) with h2449 | h2449
                                    · rcases p2446_3 (m.d 1 2) (by simp) with h2450 | h2450
                                      · rcases p2446_3 (m.d 2 3) (by simp) with h2451 | h2451
                                        · linarith only [h2451, hlam, p2446_0]
                                        · rcases p2446_3 (m.d 2 4) (by simp) with h2453 | h2453
                                          · linarith only [h2339, h2453, hlam]
                                          · linarith only [h2350, h2453, hlam]
                                      · linarith only [h2344, h2450, hlam]
                                    · linarith only [h2449, hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h2444, hc02, hlam, hphi, ht0b, ht5b, p2446_1, u5ehi9]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    rcases p2446_3 (m.d 0 2) (by simp) with h2459 | h2459
                                    · rcases p2446_3 (m.d 1 2) (by simp) with h2460 | h2460
                                      · rcases p2446_3 (m.d 2 3) (by simp) with h2461 | h2461
                                        · linarith only [h2338, h2461, hlam]
                                        · rcases p2446_3 (m.d 2 4) (by simp) with h2463 | h2463
                                          · linarith only [h2339, h2463, hlam]
                                          · linarith only [h2444, h2463, hlam]
                                      · linarith only [h2346, h2460, hlam]
                                    · linarith only [h2459, hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h0, h2337, h2348, h2442, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2446_1]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h0, h2337, h2348, h2442, hlam, p2446_2]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h2444, hc12, hlam, hphi, ht01, ht0b, ht5b, p2446_1, u5ehi9]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    rcases p2446_3 (m.d 0 2) (by simp) with h2472 | h2472
                                    · linarith only [h0, h2472, hlam]
                                    · linarith only [h2340, h2472, hlam]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h2338, hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h2344, hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h2350, hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h2442, hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h2339, hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h2345, hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    rcases p2446_3 (m.d 0 2) (by simp) with h2482 | h2482
                                    · rcases p2446_3 (m.d 1 2) (by simp) with h2483 | h2483
                                      · rcases p2446_3 (m.d 2 3) (by simp) with h2484 | h2484
                                        · linarith only [h2350, h2484, hlam]
                                        · rcases p2446_3 (m.d 2 4) (by simp) with h2486 | h2486
                                          · rcases p2446_3 (m.d 2 5) (by simp) with h2487 | h2487
                                            · linarith only [h2444, h2487, hlam]
                                            · linarith only [h2442, h2487, hlam]
                                          · linarith only [h2350, h2486, hlam]
                                      · linarith only [h2344, h2483, hlam]
                                    · linarith only [h2338, h2482, hlam]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h2338, h2341, h2350, hc02, hlam, hphi, ht0b, ht5b, p2446_1, u5ehi7]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h2340, hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h2346, hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht34, ht45, p2446_1, u5elo2]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [h2444, hlam, p2446_0]
                                  · have p2446_0 := h2446c.1
                                    have p2446_1 := h2446c.2.1
                                    have p2446_2 := h2446c.2.2.1
                                    have p2446_3 := h2446c.2.2.2
                                    linarith only [hlam, p2446_0]
                                · linarith only [h2167, h2337, h2344, h2347, h2349, h2350, h2445, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2501 | h2501
                                · rcases h2bigk with h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h0, hlam, p2502_1]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2338, h2341, h2350, h2444, h2501, hlam, p2502_2]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2338, h2341, h2444, h2501, hlam, p2502_2]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    rcases p2502_3 (m.d 0 2) (by simp) with h2507 | h2507
                                    · rcases p2502_3 (m.d 1 2) (by simp) with h2508 | h2508
                                      · rcases p2502_3 (m.d 2 3) (by simp) with h2509 | h2509
                                        · linarith only [h2338, h2509, hlam]
                                        · rcases p2502_3 (m.d 2 4) (by simp) with h2511 | h2511
                                          · linarith only [h2339, h2511, hlam]
                                          · rcases p2502_3 (m.d 2 5) (by simp) with h2513 | h2513
                                            · linarith only [h2513, hlam, p2502_0]
                                            · rcases h3bigk with h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h1750, hlam, p2515_1]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2341, h2350, h2444, h2501, hlam, p2515_2]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2338, h2350, h2444, h2501, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2515_1]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                rcases p2515_3 (m.d 0 3) (by simp) with h2520 | h2520
                                                · rcases p2515_3 (m.d 1 3) (by simp) with h2521 | h2521
                                                  · rcases p2515_3 (m.d 2 3) (by simp) with h2522 | h2522
                                                    · linarith only [h2338, h2522, hlam]
                                                    · rcases p2515_3 (m.d 3 4) (by simp) with h2524 | h2524
                                                      · linarith only [h2341, h2524, hlam]
                                                      · linarith only [h2501, h2524, hlam]
                                                  · linarith only [h2348, h2521, hlam]
                                                · linarith only [h2520, hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h1750, h2337, h2344, hc12, hlam, hphi, ht01, ht0b, ht5b, p2515_1, u5ehi6]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h1750, h2341, h2350, h2444, h2501, hlam, p2515_2]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2350, h2444, h2501, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2515_1]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                rcases p2515_3 (m.d 0 3) (by simp) with h2533 | h2533
                                                · linarith only [h1750, h2533, hlam]
                                                · linarith only [h2342, h2533, hlam]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2338, hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2344, hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2350, hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2442, hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2341, hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2347, hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                rcases p2515_3 (m.d 0 3) (by simp) with h2543 | h2543
                                                · rcases p2515_3 (m.d 1 3) (by simp) with h2544 | h2544
                                                  · rcases p2515_3 (m.d 2 3) (by simp) with h2545 | h2545
                                                    · linarith only [h2545, hlam, p2515_0]
                                                    · rcases p2515_3 (m.d 3 4) (by simp) with h2547 | h2547
                                                      · rcases p2515_3 (m.d 3 5) (by simp) with h2548 | h2548
                                                        · linarith only [h2501, h2548, hlam]
                                                        · linarith only [h2442, h2548, hlam]
                                                      · linarith only [h2547, hlam, p2515_0]
                                                  · linarith only [h2344, h2544, hlam]
                                                · linarith only [h2338, h2543, hlam]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2341, h2350, h2444, h2501, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2515_1]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2342, hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2348, hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2348, hc23, hlam, hphi, ht34, ht45, p2515_1, u5elo1]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [h2501, hlam, p2515_0]
                                              · have p2515_0 := h2515c.1
                                                have p2515_1 := h2515c.2.1
                                                have p2515_2 := h2515c.2.2.1
                                                have p2515_3 := h2515c.2.2.2
                                                linarith only [hlam, p2515_0]
                                      · linarith only [h2346, h2508, hlam]
                                    · linarith only [h2507, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h0, h2337, hc12, hlam, hphi, ht01, ht0b, ht5b, p2502_1, u5ehi6]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h0, h2337, h2349, h2350, h2444, hlam, p2502_2]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2167, h2337, h2344, h2347, h2349, h2444, hlam, p2502_2]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    rcases p2502_3 (m.d 0 2) (by simp) with h2567 | h2567
                                    · linarith only [h0, h2567, hlam]
                                    · linarith only [h2340, h2567, hlam]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2338, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2344, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2350, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2442, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2339, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2345, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2167, h2337, h2344, h2347, h2348, h2444, h2501, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2502_1]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2444, hlam, p2502_1]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2340, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2346, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht34, ht45, p2502_1, u5elo2]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2167, h2337, h2344, h2347, h2348, h2444, h2501, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2502_1]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [hlam, p2502_0]
                                · linarith only [h2350, h2501, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h2167, h2337, h2343, h2349, hc04, hlam, hphi, ht0b, ht5b, u5ehi6]
                      · linarith only [h2167, h2337, h2346, h2347, h2348, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h1750, h2337, h2346, h2347, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h0, h2337, h2346, hlam, hphi, u5ehi6, u5elo2]
                · linarith only [h1750, h2337, h2344, h2345, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h0, h2337, h2344, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h2167, h2337, h2343, hlam, hphi, u5ehi6, u5elo4]
          · linarith only [h2167, h2337, h2341, h2342, hlam, hphi, u5ehi6, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2594 | h2594
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2595 | h2595
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2596 | h2596
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2597 | h2597
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2598 | h2598
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2599 | h2599
                    · linarith only [h1750, h2337, h2341, h2596, h2598, h2599, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                    · linarith only [h1750, h2337, h2598, h2599, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h0, h2337, h2598, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                · linarith only [h0, h2339, h2597, hlam]
              · linarith only [h0, h2337, h2596, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h2167, h2337, h2595, hlam, hphi, u5ehi6, u5elo4]
          · linarith only [h1750, h2337, h2594, hlam, hphi, u5ehi6, u5elo3]
      · linarith only [h2338, h2340, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2608 | h2608
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2609 | h2609
        · linarith only [h2338, h2339, h2609, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2611 | h2611
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2612 | h2612
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2613 | h2613
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2614 | h2614
                · linarith only [h1750, h2337, h2338, h2339, h2614, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
                · linarith only [h0, h2337, h2614, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h0, h2337, h2613, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h1750, h2337, h2338, h2339, h2612, hlam, hphi, u5ehi6, u5elo4]
          · linarith only [h1750, h2337, h2611, hlam, hphi, u5ehi6, u5elo3]
      · linarith only [h1750, h2337, h2338, h2608, hlam, hphi, u5ehi6, u5elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2621 | h2621
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2622 | h2622
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2623 | h2623
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2624 | h2624
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2625 | h2625
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2626 | h2626
              · linarith only [h2338, h2622, h2626, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · linarith only [h0, h2337, h2626, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h2167, h2337, h2625, hlam, hphi, u5ehi6, u5elo4]
          · linarith only [h2167, h2337, h2338, h2621, h2624, hlam, hphi, u5ehi6, u5elo3]
        · linarith only [h2338, h2621, h2623, hlam]
      · linarith only [h2167, h2337, h2621, h2622, hlam, hphi, u5ehi6, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2633 | h2633
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2634 | h2634
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2635 | h2635
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2636 | h2636
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2637 | h2637
              · linarith only [h2338, h2633, h2637, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
              · linarith only [h0, h2337, h2637, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h2167, h2337, h2636, hlam, hphi, u5ehi6, u5elo4]
          · linarith only [h2634, h2635, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2642 | h2642
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2643 | h2643
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2644 | h2644
              · linarith only [h0, h2337, h2338, h2644, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
              · linarith only [h0, h2337, h2644, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h0, h2337, h2338, h2634, h2643, hlam, hphi, u5ehi6, u5elo4]
          · linarith only [h0, h2337, h2338, h2642, hlam, hphi, u5ehi6, u5elo3]
      · linarith only [h0, h2337, h2633, hlam, hphi, u5ehi6, u5elo2]

end R2N4
