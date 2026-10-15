import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1697 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1952 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2086 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2276 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h2277 | h2277
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2278 | h2278
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2279 | h2279
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2280 | h2280
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2281 | h2281
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2282 | h2282
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2283 | h2283
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2284 | h2284
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2285 | h2285
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2286 | h2286
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2287 | h2287
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2288 | h2288
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2289 | h2289
                          · linarith only [h2280, h2286, h2289, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                          · rcases h1bigk with h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c | h2291c
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h0, hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h1697, hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h1952, hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h2086, hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              rcases p2291_3 (m.d 0 1) (by simp) with h2297 | h2297
                              · linarith only [h2297, hlam, p2291_0]
                              · rcases p2291_3 (m.d 1 2) (by simp) with h2299 | h2299
                                · rcases p2291_3 (m.d 1 3) (by simp) with h2300 | h2300
                                  · linarith only [h2280, h2300, hlam]
                                  · linarith only [h1697, h2300, hlam]
                                · linarith only [h2299, hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h1697, h2276, h2278, h2288, h2289, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2291_1]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h1952, h2276, h2288, h2289, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2291_1]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h2086, hc01, hc12, hlam, hphi, p2291_1]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              rcases p2291_3 (m.d 0 1) (by simp) with h2308 | h2308
                              · linarith only [h2308, hlam, p2291_0]
                              · rcases p2291_3 (m.d 1 2) (by simp) with h2310 | h2310
                                · rcases p2291_3 (m.d 1 3) (by simp) with h2311 | h2311
                                  · rcases p2291_3 (m.d 1 4) (by simp) with h2312 | h2312
                                    · linarith only [h2283, h2312, hlam]
                                    · linarith only [h1952, h2312, hlam]
                                  · linarith only [h2311, hlam, p2291_0]
                                · linarith only [h0, h2310, hlam]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h2280, hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h1952, h2276, h2288, h2289, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2291_1]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h2086, h2280, hc01, hc12, hlam, hphi, p2291_1]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              rcases p2291_3 (m.d 0 1) (by simp) with h2321 | h2321
                              · linarith only [h2321, hlam, p2291_0]
                              · rcases p2291_3 (m.d 1 2) (by simp) with h2323 | h2323
                                · rcases p2291_3 (m.d 1 3) (by simp) with h2324 | h2324
                                  · rcases p2291_3 (m.d 1 4) (by simp) with h2325 | h2325
                                    · rcases p2291_3 (m.d 1 5) (by simp) with h2326 | h2326
                                      · linarith only [h2285, h2326, hlam]
                                      · linarith only [h2086, h2326, hlam]
                                    · linarith only [h2325, hlam, p2291_0]
                                  · linarith only [h1697, h2324, hlam]
                                · linarith only [h0, h2323, hlam]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h2281, hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h2283, hlam, p2291_1]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h2086, hc01, hc14, hlam, hphi, p2291_1]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2291_1, u5elo1]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h2282, hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h2284, hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [h2285, hlam, p2291_0]
                            · have p2291_0 := h2291c.1
                              have p2291_1 := h2291c.2.1
                              have p2291_2 := h2291c.2.2.1
                              have p2291_3 := h2291c.2.2.2
                              linarith only [hlam, p2291_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2341 | h2341
                          · linarith only [h2280, h2286, h2288, h2341, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases h1bigk with h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c | h2343c
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h0, hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h1697, hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h1952, hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h2086, hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              rcases p2343_3 (m.d 0 1) (by simp) with h2349 | h2349
                              · linarith only [h2349, hlam, p2343_0]
                              · rcases p2343_3 (m.d 1 2) (by simp) with h2351 | h2351
                                · rcases p2343_3 (m.d 1 3) (by simp) with h2352 | h2352
                                  · linarith only [h2280, h2352, hlam]
                                  · linarith only [h1697, h2352, hlam]
                                · linarith only [h2351, hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h1697, hc01, hc12, hlam, hphi, p2343_1]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h1952, h2279, h2286, h2288, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2343_1]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h2086, hc01, hc12, hlam, hphi, p2343_1]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              rcases p2343_3 (m.d 0 1) (by simp) with h2360 | h2360
                              · linarith only [h2360, hlam, p2343_0]
                              · rcases p2343_3 (m.d 1 2) (by simp) with h2362 | h2362
                                · rcases p2343_3 (m.d 1 3) (by simp) with h2363 | h2363
                                  · rcases p2343_3 (m.d 1 4) (by simp) with h2364 | h2364
                                    · linarith only [h2283, h2364, hlam]
                                    · linarith only [h1952, h2364, hlam]
                                  · linarith only [h2363, hlam, p2343_0]
                                · linarith only [h0, h2362, hlam]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h2280, hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h1952, h2279, h2286, h2288, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2343_1]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h2086, h2280, hc01, hc12, hlam, hphi, p2343_1]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              rcases p2343_3 (m.d 0 1) (by simp) with h2373 | h2373
                              · linarith only [h2373, hlam, p2343_0]
                              · rcases p2343_3 (m.d 1 2) (by simp) with h2375 | h2375
                                · rcases p2343_3 (m.d 1 3) (by simp) with h2376 | h2376
                                  · rcases p2343_3 (m.d 1 4) (by simp) with h2377 | h2377
                                    · rcases p2343_3 (m.d 1 5) (by simp) with h2378 | h2378
                                      · linarith only [h2285, h2378, hlam]
                                      · linarith only [h2086, h2378, hlam]
                                    · linarith only [h2377, hlam, p2343_0]
                                  · linarith only [h1697, h2376, hlam]
                                · linarith only [h0, h2375, hlam]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h2281, hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h2283, hlam, p2343_1]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h2086, hc01, hc14, hlam, hphi, p2343_1]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2343_1, u5elo1]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h2282, hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h2284, hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [h2285, hlam, p2343_0]
                            · have p2343_0 := h2343c.1
                              have p2343_1 := h2343c.2.1
                              have p2343_2 := h2343c.2.2.1
                              have p2343_3 := h2343c.2.2.2
                              linarith only [hlam, p2343_0]
                      · linarith only [h2284, h2286, h2287, hc34, hlam, hphi, ht45, u5elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2394 | h2394
                      · linarith only [h1697, h2278, h2280, h2286, h2394, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2396 | h2396
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2397 | h2397
                          · rcases h1bigk with h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c | h2398c
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h0, hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h1697, hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h1952, hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h2086, hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              rcases p2398_3 (m.d 0 1) (by simp) with h2404 | h2404
                              · linarith only [h2404, hlam, p2398_0]
                              · rcases p2398_3 (m.d 1 2) (by simp) with h2406 | h2406
                                · rcases p2398_3 (m.d 1 3) (by simp) with h2407 | h2407
                                  · linarith only [h2280, h2407, hlam]
                                  · linarith only [h1697, h2407, hlam]
                                · linarith only [h2406, hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h1697, hc01, hc12, hlam, hphi, p2398_1]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h1952, h2276, h2396, hc12, hlam, hphi, ht01, ht0b, ht5b, p2398_1, u5ehi9]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h2086, hc01, hc12, hlam, hphi, p2398_1]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              rcases p2398_3 (m.d 0 1) (by simp) with h2415 | h2415
                              · linarith only [h2415, hlam, p2398_0]
                              · rcases p2398_3 (m.d 1 2) (by simp) with h2417 | h2417
                                · rcases p2398_3 (m.d 1 3) (by simp) with h2418 | h2418
                                  · rcases p2398_3 (m.d 1 4) (by simp) with h2419 | h2419
                                    · linarith only [h2283, h2419, hlam]
                                    · linarith only [h1952, h2419, hlam]
                                  · linarith only [h2418, hlam, p2398_0]
                                · linarith only [h0, h2417, hlam]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h2280, hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h1952, h2278, h2286, h2396, hc13, hlam, hphi, ht01, ht0b, ht5b, p2398_1, u5ehi9]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h2086, h2280, hc01, hc12, hlam, hphi, p2398_1]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              rcases p2398_3 (m.d 0 1) (by simp) with h2428 | h2428
                              · linarith only [h2428, hlam, p2398_0]
                              · rcases p2398_3 (m.d 1 2) (by simp) with h2430 | h2430
                                · rcases p2398_3 (m.d 1 3) (by simp) with h2431 | h2431
                                  · rcases p2398_3 (m.d 1 4) (by simp) with h2432 | h2432
                                    · rcases p2398_3 (m.d 1 5) (by simp) with h2433 | h2433
                                      · linarith only [h2285, h2433, hlam]
                                      · linarith only [h2086, h2433, hlam]
                                    · linarith only [h2432, hlam, p2398_0]
                                  · linarith only [h1697, h2431, hlam]
                                · linarith only [h0, h2430, hlam]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h2281, hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h2283, hlam, p2398_1]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h2086, hc01, hc14, hlam, hphi, p2398_1]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2398_1, u5elo1]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h2282, hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h2284, hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [h2285, hlam, p2398_0]
                            · have p2398_0 := h2398c.1
                              have p2398_1 := h2398c.2.1
                              have p2398_2 := h2398c.2.2.1
                              have p2398_3 := h2398c.2.2.2
                              linarith only [hlam, p2398_0]
                          · linarith only [h2286, h2396, h2397, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2449 | h2449
                          · rcases h1bigk with h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c | h2450c
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h0, hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h1697, hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h1952, hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h2086, hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              rcases p2450_3 (m.d 0 1) (by simp) with h2456 | h2456
                              · linarith only [h2456, hlam, p2450_0]
                              · rcases p2450_3 (m.d 1 2) (by simp) with h2458 | h2458
                                · rcases p2450_3 (m.d 1 3) (by simp) with h2459 | h2459
                                  · linarith only [h2280, h2459, hlam]
                                  · linarith only [h1697, h2459, hlam]
                                · linarith only [h2458, hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h1697, h2278, h2396, h2449, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2450_1]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h1952, hc01, hc12, hlam, hphi, p2450_1]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h2086, hc01, hc12, hlam, hphi, p2450_1]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              rcases p2450_3 (m.d 0 1) (by simp) with h2467 | h2467
                              · linarith only [h2467, hlam, p2450_0]
                              · rcases p2450_3 (m.d 1 2) (by simp) with h2469 | h2469
                                · rcases p2450_3 (m.d 1 3) (by simp) with h2470 | h2470
                                  · rcases p2450_3 (m.d 1 4) (by simp) with h2471 | h2471
                                    · linarith only [h2283, h2471, hlam]
                                    · linarith only [h1952, h2471, hlam]
                                  · linarith only [h2470, hlam, p2450_0]
                                · linarith only [h0, h2469, hlam]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h2280, hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h1952, h2278, h2286, h2396, h2449, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2450_1]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h2086, h2280, hc01, hc12, hlam, hphi, p2450_1]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              rcases p2450_3 (m.d 0 1) (by simp) with h2480 | h2480
                              · linarith only [h2480, hlam, p2450_0]
                              · rcases p2450_3 (m.d 1 2) (by simp) with h2482 | h2482
                                · rcases p2450_3 (m.d 1 3) (by simp) with h2483 | h2483
                                  · rcases p2450_3 (m.d 1 4) (by simp) with h2484 | h2484
                                    · rcases p2450_3 (m.d 1 5) (by simp) with h2485 | h2485
                                      · linarith only [h2285, h2485, hlam]
                                      · linarith only [h2086, h2485, hlam]
                                    · linarith only [h2484, hlam, p2450_0]
                                  · linarith only [h1697, h2483, hlam]
                                · linarith only [h0, h2482, hlam]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h2281, hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h2283, hlam, p2450_1]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h2086, hc01, hc14, hlam, hphi, p2450_1]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2450_1, u5elo1]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h2282, hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h2284, hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [h2285, hlam, p2450_0]
                            · have p2450_0 := h2450c.1
                              have p2450_1 := h2450c.2.1
                              have p2450_2 := h2450c.2.2.1
                              have p2450_3 := h2450c.2.2.2
                              linarith only [hlam, p2450_0]
                          · linarith only [h2279, h2286, h2449, hc23, hlam, hphi, ht34, ht45, u5elo0]
                  · linarith only [h1952, h2086, h2279, h2285, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                · linarith only [h1697, h2284, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h1697, h2278, h2283, hlam]
            · linarith only [h0, h2282, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h1697, h2276, h2278, h2279, h2280, h2281, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2506 | h2506
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2507 | h2507
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2508 | h2508
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2509 | h2509
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2510 | h2510
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2511 | h2511
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2512 | h2512
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2513 | h2513
                        · linarith only [h0, h2276, h2280, h2513, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2515 | h2515
                          · linarith only [h2511, h2513, h2515, hlam]
                          · rcases h1bigk with h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [hlam, p2517_0]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h0, hlam, p2517_0]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h1697, hlam, p2517_0]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h1952, hlam, p2517_0]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h2086, hlam, p2517_0]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h2280, hc01, hc23, hlam, hphi, ht12, p2517_1]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [hlam, p2517_0]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h2280, hlam, p2517_1]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h1952, h2279, h2280, h2511, h2513, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2517_1]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h2086, h2280, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2517_1, u5ehi5]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              rcases p2517_3 (m.d 0 1) (by simp) with h2528 | h2528
                              · linarith only [h2528, hlam, p2517_0]
                              · rcases p2517_3 (m.d 1 2) (by simp) with h2530 | h2530
                                · linarith only [h2280, h2530, hlam]
                                · linarith only [h0, h2530, hlam]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h0, hc01, hc13, hlam, hphi, p2517_1]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [hlam, p2517_0]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h1952, h2279, h2280, h2511, h2513, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2517_1]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h2086, h2280, hc01, hc23, hlam, hphi, ht12, p2517_1]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h2280, h2506, hc01, hc23, hlam, hphi, ht12, p2517_1]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h2506, hlam, p2517_0]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h2508, hlam, p2517_1]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [hlam, p2517_0]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h2086, h2280, h2506, hc01, hc23, hlam, hphi, ht12, p2517_1]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2517_1, u5elo1]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h2507, hlam, p2517_0]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h2509, hlam, p2517_0]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [h2510, hlam, p2517_0]
                            · have p2517_0 := h2517c.1
                              have p2517_1 := h2517c.2.1
                              have p2517_2 := h2517c.2.2.1
                              have p2517_3 := h2517c.2.2.2
                              linarith only [hlam, p2517_0]
                      · linarith only [h0, h2276, h2279, h2280, h2512, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                    · linarith only [h0, h2280, h2511, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h1952, h2276, h2279, h2510, hc01, hc12, hlam, hphi]
                · linarith only [h1697, h2509, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h2277, h2278, h2280, h2508, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
            · linarith only [h0, h2276, h2277, h2279, h2507, hlam, hphi, u5ehi9, u5elo0]
          · linarith only [h0, h2276, h2506, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2554 | h2554
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2555 | h2555
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2556 | h2556
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2557 | h2557
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2558 | h2558
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2559 | h2559
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2560 | h2560
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2561 | h2561
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2562 | h2562
                        · linarith only [h2276, h2279, h2562, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2564 | h2564
                          · linarith only [h2276, h2279, h2560, h2564, hlam]
                          · rcases h1bigk with h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c | h2566c
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h0, hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h1697, hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h1952, hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h2086, hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              rcases p2566_3 (m.d 0 1) (by simp) with h2572 | h2572
                              · linarith only [h2572, hlam, p2566_0]
                              · rcases p2566_3 (m.d 1 2) (by simp) with h2574 | h2574
                                · rcases p2566_3 (m.d 1 3) (by simp) with h2575 | h2575
                                  · linarith only [h2554, h2575, hlam]
                                  · linarith only [h1697, h2575, hlam]
                                · linarith only [h2574, hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h1697, hc01, hc12, hlam, hphi, p2566_1]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h2279, h2559, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2566_1]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h2086, hc01, hc12, hlam, hphi, p2566_1]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              rcases p2566_3 (m.d 0 1) (by simp) with h2583 | h2583
                              · linarith only [h2583, hlam, p2566_0]
                              · rcases p2566_3 (m.d 1 2) (by simp) with h2585 | h2585
                                · rcases p2566_3 (m.d 1 3) (by simp) with h2586 | h2586
                                  · rcases p2566_3 (m.d 1 4) (by simp) with h2587 | h2587
                                    · linarith only [h2557, h2587, hlam]
                                    · linarith only [h1952, h2587, hlam]
                                  · linarith only [h2586, hlam, p2566_0]
                                · linarith only [h0, h2585, hlam]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h2554, hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h1952, h2279, h2559, hc01, hc13, hlam, hphi, p2566_1]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h1952, h2279, h2554, h2559, hc01, hc12, hlam, hphi, p2566_1]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              rcases p2566_3 (m.d 0 1) (by simp) with h2596 | h2596
                              · linarith only [h2596, hlam, p2566_0]
                              · rcases p2566_3 (m.d 1 2) (by simp) with h2598 | h2598
                                · rcases p2566_3 (m.d 1 3) (by simp) with h2599 | h2599
                                  · rcases p2566_3 (m.d 1 4) (by simp) with h2600 | h2600
                                    · rcases p2566_3 (m.d 1 5) (by simp) with h2601 | h2601
                                      · linarith only [h2559, h2601, hlam]
                                      · linarith only [h2086, h2601, hlam]
                                    · linarith only [h2600, hlam, p2566_0]
                                  · linarith only [h1697, h2599, hlam]
                                · linarith only [h0, h2598, hlam]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h2555, hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h2557, hlam, p2566_1]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h1952, h2279, h2559, hc01, hc14, hlam, hphi, p2566_1]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2566_1, u5elo1]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h2556, hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h2558, hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [h2559, hlam, p2566_0]
                            · have p2566_0 := h2566c.1
                              have p2566_1 := h2566c.2.1
                              have p2566_2 := h2566c.2.2.1
                              have p2566_3 := h2566c.2.2.2
                              linarith only [hlam, p2566_0]
                      · linarith only [h2558, h2560, h2561, hc34, hlam, hphi, ht45, u5elo1]
                    · linarith only [h2278, h2279, h2559, h2560, hc23, hlam, hphi, ht34, ht45, u5elo1]
                  · linarith only [h1952, h2559, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h1697, h2558, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h1697, h2278, h2557, hlam]
            · linarith only [h0, h2556, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h2276, h2555, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2623 | h2623
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2624 | h2624
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2625 | h2625
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2626 | h2626
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2627 | h2627
                  · linarith only [h1952, h2279, h2554, h2623, h2627, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h1952, h2627, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h2554, h2626, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h2277, h2278, h2279, h2554, h2625, hlam, hphi, u5ehi7, u5elo4]
            · linarith only [h0, h2277, h2624, hlam]
          · linarith only [h0, h2276, h2277, h2279, h2623, hlam, hphi, u5ehi7, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2634 | h2634
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2635 | h2635
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2636 | h2636
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2637 | h2637
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2638 | h2638
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2639 | h2639
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2640 | h2640
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2641 | h2641
                    · linarith only [h2278, h2634, h2635, h2641, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2643 | h2643
                      · linarith only [h2638, h2641, h2643, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2645 | h2645
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2646 | h2646
                          · rcases h1bigk with h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c | h2647c
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h0, hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h1697, hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h1952, hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h2086, hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              rcases p2647_3 (m.d 0 1) (by simp) with h2653 | h2653
                              · linarith only [h2653, hlam, p2647_0]
                              · rcases p2647_3 (m.d 1 2) (by simp) with h2655 | h2655
                                · rcases p2647_3 (m.d 1 3) (by simp) with h2656 | h2656
                                  · linarith only [h2635, h2656, hlam]
                                  · linarith only [h1697, h2656, hlam]
                                · linarith only [h2655, hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h1697, hc01, hc12, hlam, hphi, p2647_1]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h1952, hc01, hc12, hlam, hphi, p2647_1]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h2086, hc01, hc12, hlam, hphi, p2647_1]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              rcases p2647_3 (m.d 0 1) (by simp) with h2664 | h2664
                              · linarith only [h2664, hlam, p2647_0]
                              · rcases p2647_3 (m.d 1 2) (by simp) with h2666 | h2666
                                · rcases p2647_3 (m.d 1 3) (by simp) with h2667 | h2667
                                  · rcases p2647_3 (m.d 1 4) (by simp) with h2668 | h2668
                                    · linarith only [h2638, h2668, hlam]
                                    · linarith only [h1952, h2668, hlam]
                                  · linarith only [h2667, hlam, p2647_0]
                                · linarith only [h0, h2666, hlam]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h2635, hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h2276, h2278, h2638, h2645, hc13, hlam, hphi, ht01, ht0b, ht5b, p2647_1, u5ehi9]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h2086, h2635, hc01, hc12, hlam, hphi, p2647_1]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              rcases p2647_3 (m.d 0 1) (by simp) with h2677 | h2677
                              · linarith only [h2677, hlam, p2647_0]
                              · rcases p2647_3 (m.d 1 2) (by simp) with h2679 | h2679
                                · rcases p2647_3 (m.d 1 3) (by simp) with h2680 | h2680
                                  · rcases p2647_3 (m.d 1 4) (by simp) with h2681 | h2681
                                    · rcases p2647_3 (m.d 1 5) (by simp) with h2682 | h2682
                                      · linarith only [h2640, h2682, hlam]
                                      · linarith only [h2086, h2682, hlam]
                                    · linarith only [h2681, hlam, p2647_0]
                                  · linarith only [h1697, h2680, hlam]
                                · linarith only [h0, h2679, hlam]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h2636, hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h2638, hlam, p2647_1]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h2086, hc01, hc14, hlam, hphi, p2647_1]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2647_1, u5elo1]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h2637, hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h2639, hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [h2640, hlam, p2647_0]
                            · have p2647_0 := h2647c.1
                              have p2647_1 := h2647c.2.1
                              have p2647_2 := h2647c.2.2.1
                              have p2647_3 := h2647c.2.2.2
                              linarith only [hlam, p2647_0]
                          · linarith only [h2276, h2278, h2645, h2646, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2698 | h2698
                          · rcases h1bigk with h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c | h2699c
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h0, hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h1697, hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h1952, hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h2086, hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              rcases p2699_3 (m.d 0 1) (by simp) with h2705 | h2705
                              · linarith only [h2705, hlam, p2699_0]
                              · rcases p2699_3 (m.d 1 2) (by simp) with h2707 | h2707
                                · rcases p2699_3 (m.d 1 3) (by simp) with h2708 | h2708
                                  · linarith only [h2635, h2708, hlam]
                                  · linarith only [h1697, h2708, hlam]
                                · linarith only [h2707, hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h2278, h2634, h2638, h2641, h2645, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2699_1]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h1952, hc01, hc12, hlam, hphi, p2699_1]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h2086, hc01, hc12, hlam, hphi, p2699_1]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              rcases p2699_3 (m.d 0 1) (by simp) with h2716 | h2716
                              · linarith only [h2716, hlam, p2699_0]
                              · rcases p2699_3 (m.d 1 2) (by simp) with h2718 | h2718
                                · rcases p2699_3 (m.d 1 3) (by simp) with h2719 | h2719
                                  · rcases p2699_3 (m.d 1 4) (by simp) with h2720 | h2720
                                    · linarith only [h2638, h2720, hlam]
                                    · linarith only [h1952, h2720, hlam]
                                  · linarith only [h2719, hlam, p2699_0]
                                · linarith only [h0, h2718, hlam]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h2635, hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h2278, h2634, h2638, h2641, h2645, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2699_1]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h2086, h2635, hc01, hc12, hlam, hphi, p2699_1]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              rcases p2699_3 (m.d 0 1) (by simp) with h2729 | h2729
                              · linarith only [h2729, hlam, p2699_0]
                              · rcases p2699_3 (m.d 1 2) (by simp) with h2731 | h2731
                                · rcases p2699_3 (m.d 1 3) (by simp) with h2732 | h2732
                                  · rcases p2699_3 (m.d 1 4) (by simp) with h2733 | h2733
                                    · rcases p2699_3 (m.d 1 5) (by simp) with h2734 | h2734
                                      · linarith only [h2640, h2734, hlam]
                                      · linarith only [h2086, h2734, hlam]
                                    · linarith only [h2733, hlam, p2699_0]
                                  · linarith only [h1697, h2732, hlam]
                                · linarith only [h0, h2731, hlam]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h2636, hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h2638, hlam, p2699_1]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h2086, hc01, hc14, hlam, hphi, p2699_1]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2699_1, u5elo1]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h2637, hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h2639, hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [h2640, hlam, p2699_0]
                            · have p2699_0 := h2699c.1
                              have p2699_1 := h2699c.2.1
                              have p2699_2 := h2699c.2.2.1
                              have p2699_3 := h2699c.2.2.2
                              linarith only [hlam, p2699_0]
                          · linarith only [h2278, h2634, h2698, hlam]
                  · linarith only [h1952, h2278, h2634, h2635, h2638, h2640, hc01, hc12, hlam, hphi]
                · linarith only [h2278, h2634, h2638, h2639, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2752 | h2752
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2753 | h2753
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2754 | h2754
                    · linarith only [h2638, h2752, h2754, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2756 | h2756
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2757 | h2757
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2758 | h2758
                          · rcases h1bigk with h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c | h2759c
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h0, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h1697, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h1952, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2086, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              rcases p2759_3 (m.d 0 1) (by simp) with h2765 | h2765
                              · linarith only [h2765, hlam, p2759_0]
                              · rcases p2759_3 (m.d 1 2) (by simp) with h2767 | h2767
                                · rcases p2759_3 (m.d 1 3) (by simp) with h2768 | h2768
                                  · linarith only [h2635, h2768, hlam]
                                  · linarith only [h1697, h2768, hlam]
                                · linarith only [h2767, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2635, h2756, h2758, hc12, hlam, hphi, ht01, ht0b, ht5b, p2759_1, u5ehi9]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h1952, h2276, h2754, h2756, h2758, hc12, hlam, hphi, ht01, ht0b, ht5b, p2759_1, u5ehi9]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2086, hc01, hc12, hlam, hphi, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2638, hc01, hc34, hlam, hphi, ht12, ht23, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2635, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2638, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2086, hc01, hc13, hlam, hphi, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              rcases p2759_3 (m.d 0 1) (by simp) with h2781 | h2781
                              · linarith only [h2781, hlam, p2759_0]
                              · rcases p2759_3 (m.d 1 2) (by simp) with h2783 | h2783
                                · rcases p2759_3 (m.d 1 3) (by simp) with h2784 | h2784
                                  · linarith only [h2638, h2784, hlam]
                                  · linarith only [h1697, h2784, hlam]
                                · linarith only [h0, h2783, hlam]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2636, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h1697, h2638, hc01, hc34, hlam, hphi, ht12, ht23, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2086, h2638, hc01, hc34, hlam, hphi, ht12, ht23, p2759_1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2759_1, u5elo1]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2637, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2752, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [h2753, hlam, p2759_0]
                            · have p2759_0 := h2759c.1
                              have p2759_1 := h2759c.2.1
                              have p2759_2 := h2759c.2.2.1
                              have p2759_3 := h2759c.2.2.2
                              linarith only [hlam, p2759_0]
                          · linarith only [h2635, h2638, h2756, h2758, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                        · linarith only [h2634, h2754, h2756, h2757, hlam, hphi, u5ehi8, u5elo0]
                      · linarith only [h2638, h2752, h2756, hc23, hc34, hlam, hphi]
                  · linarith only [h1952, h2753, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h1697, h2752, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h2637, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h2276, h2636, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2804 | h2804
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2805 | h2805
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2806 | h2806
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2807 | h2807
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2808 | h2808
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2809 | h2809
                    · linarith only [h0, h2276, h2278, h2634, h2635, h2809, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                    · linarith only [h0, h2276, h2635, h2806, h2809, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h1952, h2808, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h1697, h2278, h2634, h2635, h2804, h2806, h2807, hc01, hc23, hlam, hphi, ht12, u5ehi9, u5elo3]
              · linarith only [h2635, h2804, h2806, hlam]
            · linarith only [h0, h2276, h2805, hc24, hlam, hphi, ht45, u5elo2]
          · linarith only [h0, h2276, h2804, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2817 | h2817
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2818 | h2818
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2819 | h2819
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2820 | h2820
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2821 | h2821
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2822 | h2822
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2823 | h2823
                    · linarith only [h1697, h2278, h2817, h2823, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2825 | h2825
                      · linarith only [h2276, h2634, h2822, h2823, h2825, hlam, hphi, u5ehi8, u5elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2827 | h2827
                        · linarith only [h2276, h2634, h2827, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2829 | h2829
                          · linarith only [h1952, h2634, h2820, h2829, hc01, hc13, hlam, hphi]
                          · linarith only [h1697, h2278, h2822, h2829, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h1952, h2822, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h1697, h2821, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2834 | h2834
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2835 | h2835
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2836 | h2836
                    · linarith only [h2820, h2834, h2836, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2838 | h2838
                      · linarith only [h2276, h2634, h2835, h2836, h2838, hlam, hphi, u5ehi8, u5elo1]
                      · linarith only [h2820, h2834, h2838, hc23, hc34, hlam, hphi]
                  · linarith only [h1952, h2835, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h1697, h2834, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h2819, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h2276, h2818, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2845 | h2845
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2846 | h2846
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2847 | h2847
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2848 | h2848
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2849 | h2849
                  · linarith only [h1952, h2634, h2817, h2845, h2849, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h1952, h2849, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h1697, h2278, h2847, h2848, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h2817, h2845, h2847, hlam]
            · linarith only [h0, h2277, h2846, hlam]
          · linarith only [h0, h2276, h2845, hlam]
  · linarith only [h2276, h2277, hc24, hlam, hphi, ht45, u5elo2]

end R2N4
