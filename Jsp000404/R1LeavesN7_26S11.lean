import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_26S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5518000 in
set_option maxHeartbeats 5518000 in
theorem r1l7_13_24_L_I_M_IR_s0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h2316 | h2316
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2317 | h2317
    · linarith only [h0, h1, h2317, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2319 | h2319
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2320 | h2320
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2321 | h2321
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2322 | h2322
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2323 | h2323
              · linarith only [h2317, h2319, h2322, h2323, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2325 | h2325
                · linarith only [h0, h1, h2325, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h1, h2319, h2323, h2325, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2328 | h2328
              · linarith only [h0, h2317, h2319, h2328, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2330 | h2330
                · linarith only [h0, h1, h2328, h2330, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · linarith only [h0, h1, h2319, h2328, h2330, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2333 | h2333
            · linarith only [h1, h2316, h2321, h2333, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2335 | h2335
              · linarith only [h0, h1, h2321, h2335, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2337 | h2337
                · linarith only [h0, h1, h2321, h2337, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · linarith only [h0, h1, h2319, h2321, h2337, hc12, hc35, hlam, hphi, ht23]
        · linarith only [h1, h2316, h2320, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2341 | h2341
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2342 | h2342
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2343 | h2343
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2344 | h2344
              · linarith only [h0, h1, h2317, h2344, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2346 | h2346
                · linarith only [h0, h1, h2319, h2343, h2344, h2346, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2348 | h2348
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2349 | h2349
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2350 | h2350
                      · linarith only [h1, h2316, h2344, h2350, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h1, h2316, h2343, h2344, h2346, h2350, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h2316, h2342, h2349, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h1, h2316, h2343, h2348, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2355 | h2355
              · linarith only [h0, h2317, h2355, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2357 | h2357
                · linarith only [h0, h2319, h2357, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2359 | h2359
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2360 | h2360
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2361 | h2361
                      · linarith only [h2316, h2343, h2361, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2363 | h2363
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2364 | h2364
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2365 | h2365
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2366 | h2366
                              · linarith only [h2316, h2343, h2359, h2366, hlam]
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
                                  linarith only [h1, hlam, p2368_1]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h2317, hlam, p2368_1]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  rcases p2368_3 (m.d 0 3) (by simp) with h2372 | h2372
                                  · rcases p2368_3 (m.d 1 3) (by simp) with h2373 | h2373
                                    · rcases p2368_3 (m.d 2 3) (by simp) with h2374 | h2374
                                      · rcases p2368_3 (m.d 3 4) (by simp) with h2375 | h2375
                                        · linarith only [h2375, hlam, p2368_0]
                                        · rcases p2368_3 (m.d 3 5) (by simp) with h2377 | h2377
                                          · linarith only [h2342, h2377, hlam]
                                          · linarith only [h2366, h2377, hlam]
                                      · linarith only [h2363, h2374, hlam]
                                    · linarith only [h2359, h2373, hlam]
                                  · linarith only [h2372, hlam, p2368_0]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  rcases p2368_3 (m.d 0 3) (by simp) with h2383 | h2383
                                  · rcases p2368_3 (m.d 1 3) (by simp) with h2384 | h2384
                                    · rcases p2368_3 (m.d 2 3) (by simp) with h2385 | h2385
                                      · rcases p2368_3 (m.d 3 4) (by simp) with h2386 | h2386
                                        · linarith only [h2341, h2386, hlam]
                                        · rcases p2368_3 (m.d 3 5) (by simp) with h2388 | h2388
                                          · linarith only [h2388, hlam, p2368_0]
                                          · rcases h4bigk with h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [hlam, p2390_0]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2343, h2359, h2365, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2390_1, u4ehi3]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2319, hlam, p2390_0]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2343, h2365, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2390_1, u4ehi3]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2343, hlam, p2390_0]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2316, hlam, p2390_1]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [hlam, p2390_0]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2357, hlam, p2390_0]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h1, h2316, h2355, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2390_1, u4ehi3]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2361, hlam, p2390_0]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              rcases p2390_3 (m.d 0 4) (by simp) with h2401 | h2401
                                              · linarith only [h2319, h2401, hlam]
                                              · rcases p2390_3 (m.d 1 4) (by simp) with h2403 | h2403
                                                · linarith only [h2357, h2403, hlam]
                                                · rcases p2390_3 (m.d 2 4) (by simp) with h2405 | h2405
                                                  · rcases p2390_3 (m.d 3 4) (by simp) with h2406 | h2406
                                                    · linarith only [h2363, h2406, hlam]
                                                    · rcases p2390_3 (m.d 4 5) (by simp) with h2408 | h2408
                                                      · linarith only [h2365, h2408, hlam]
                                                      · linarith only [h2343, h2408, hlam]
                                                  · linarith only [h2319, h2405, hlam]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              rcases p2390_3 (m.d 0 4) (by simp) with h2412 | h2412
                                              · linarith only [h2319, h2412, hlam]
                                              · linarith only [h2316, h2412, hlam]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [hlam, p2390_0]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              rcases p2390_3 (m.d 0 4) (by simp) with h2416 | h2416
                                              · linarith only [h2319, h2416, hlam]
                                              · linarith only [h2341, h2416, hlam]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2319, h2343, h2363, hc02, hc23, hlam, hphi, p2390_1]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2341, hlam, p2390_1]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2359, hlam, p2390_0]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2363, hlam, p2390_0]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [hlam, p2390_0]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2366, hlam, p2390_0]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2316, hc45, hlam, hphi, p2390_1, u4ehi1]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2359, hc45, hlam, hphi, p2390_1, u4ehi3]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2365, hlam, p2390_0]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [h2363, h2365, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2390_1, u4ehi3]
                                            · have p2390_0 := h2390c.1
                                              have p2390_1 := h2390c.2.1
                                              have p2390_2 := h2390c.2.2.1
                                              have p2390_3 := h2390c.2.2.2
                                              linarith only [hlam, p2390_0]
                                      · linarith only [h2364, h2385, hlam]
                                    · linarith only [h2360, h2384, hlam]
                                  · linarith only [h2383, hlam, p2368_0]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h0, h1, h2355, hc12, hc23, hlam, hphi, p2368_1]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [hlam, p2368_0]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h2355, hlam, p2368_1]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  rcases p2368_3 (m.d 0 3) (by simp) with h2436 | h2436
                                  · linarith only [h1, h2436, hlam]
                                  · linarith only [h2341, h2436, hlam]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  rcases p2368_3 (m.d 0 3) (by simp) with h2439 | h2439
                                  · linarith only [h1, h2439, hlam]
                                  · linarith only [h2342, h2439, hlam]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h1, h2316, h2359, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2368_1, u4ehi3]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h1, h2316, h2359, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2368_1, u4ehi3]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [hlam, p2368_0]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  rcases p2368_3 (m.d 0 3) (by simp) with h2445 | h2445
                                  · linarith only [h2317, h2445, hlam]
                                  · linarith only [h2341, h2445, hlam]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  rcases p2368_3 (m.d 0 3) (by simp) with h2448 | h2448
                                  · linarith only [h2317, h2448, hlam]
                                  · linarith only [h2342, h2448, hlam]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h2341, hlam, p2368_0]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h2359, hlam, p2368_0]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h2363, hlam, p2368_0]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [hlam, p2368_0]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h2366, hlam, p2368_1]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h2342, hlam, p2368_0]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h2360, hlam, p2368_0]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h2364, hlam, p2368_0]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [h2342, hc03, hlam, hphi, ht0b, ht45, ht5b, p2368_1, u4ehi3]
                                · have p2368_0 := h2368c.1
                                  have p2368_1 := h2368c.2.1
                                  have p2368_2 := h2368c.2.2.1
                                  have p2368_3 := h2368c.2.2.2
                                  linarith only [hlam, p2368_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2461 | h2461
                              · linarith only [h2316, h2359, h2365, h2461, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                              · rcases h3bigk with h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [hlam, p2463_0]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h1, hlam, p2463_1]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h2317, hlam, p2463_1]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  rcases p2463_3 (m.d 0 3) (by simp) with h2467 | h2467
                                  · rcases p2463_3 (m.d 1 3) (by simp) with h2468 | h2468
                                    · rcases p2463_3 (m.d 2 3) (by simp) with h2469 | h2469
                                      · rcases p2463_3 (m.d 3 4) (by simp) with h2470 | h2470
                                        · linarith only [h2470, hlam, p2463_0]
                                        · rcases p2463_3 (m.d 3 5) (by simp) with h2472 | h2472
                                          · linarith only [h2342, h2472, hlam]
                                          · linarith only [h2461, h2472, hlam]
                                      · linarith only [h2363, h2469, hlam]
                                    · linarith only [h2359, h2468, hlam]
                                  · linarith only [h2467, hlam, p2463_0]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  rcases p2463_3 (m.d 0 3) (by simp) with h2478 | h2478
                                  · rcases p2463_3 (m.d 1 3) (by simp) with h2479 | h2479
                                    · rcases p2463_3 (m.d 2 3) (by simp) with h2480 | h2480
                                      · rcases p2463_3 (m.d 3 4) (by simp) with h2481 | h2481
                                        · linarith only [h2341, h2481, hlam]
                                        · rcases p2463_3 (m.d 3 5) (by simp) with h2483 | h2483
                                          · linarith only [h2483, hlam, p2463_0]
                                          · rcases h4bigk with h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [hlam, p2485_0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h1, h2316, h2355, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2485_1, u4ehi1]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2319, hlam, p2485_0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2319, h2365, hc45, hlam, hphi, p2485_1, u4ehi3]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2343, hlam, p2485_0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2316, hlam, p2485_1]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [hlam, p2485_0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2357, hlam, p2485_0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h1, h2316, h2355, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2485_1, u4ehi3]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2361, hlam, p2485_0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2365, hc45, hlam, hphi, p2485_1, u4ehi0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2365, hc45, hlam, hphi, p2485_1, u4ehi1]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [hlam, p2485_0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2365, hc45, hlam, hphi, p2485_1, u4ehi3]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2365, hlam, p2485_0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2341, hlam, p2485_1]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2359, hlam, p2485_0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2363, hlam, p2485_0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [hlam, p2485_0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2461, hlam, p2485_0]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2316, h2359, hc45, hlam, hphi, p2485_1, u4ehi3]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [h2359, hc45, hlam, hphi, p2485_1, u4ehi3]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [hc45, hlam, hphi, p2485_1, u4ehi2]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [hc45, hlam, hphi, p2485_1, u4ehi3]
                                            · have p2485_0 := h2485c.1
                                              have p2485_1 := h2485c.2.1
                                              have p2485_2 := h2485c.2.2.1
                                              have p2485_3 := h2485c.2.2.2
                                              linarith only [hlam, p2485_0]
                                      · linarith only [h2364, h2480, hlam]
                                    · linarith only [h2360, h2479, hlam]
                                  · linarith only [h2478, hlam, p2463_0]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h0, h1, h2355, hc12, hc23, hlam, hphi, p2463_1]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [hlam, p2463_0]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h2355, hlam, p2463_1]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  rcases p2463_3 (m.d 0 3) (by simp) with h2517 | h2517
                                  · linarith only [h1, h2517, hlam]
                                  · linarith only [h2341, h2517, hlam]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  rcases p2463_3 (m.d 0 3) (by simp) with h2520 | h2520
                                  · linarith only [h1, h2520, hlam]
                                  · linarith only [h2342, h2520, hlam]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h1, h2316, h2359, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2463_1, u4ehi3]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h1, h2316, h2359, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2463_1, u4ehi3]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [hlam, p2463_0]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  rcases p2463_3 (m.d 0 3) (by simp) with h2526 | h2526
                                  · linarith only [h2317, h2526, hlam]
                                  · linarith only [h2341, h2526, hlam]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  rcases p2463_3 (m.d 0 3) (by simp) with h2529 | h2529
                                  · linarith only [h2317, h2529, hlam]
                                  · linarith only [h2342, h2529, hlam]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h2341, hlam, p2463_0]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h2359, hlam, p2463_0]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h2363, hlam, p2463_0]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [hlam, p2463_0]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h2461, hlam, p2463_1]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h2342, hlam, p2463_0]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h2360, hlam, p2463_0]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h2364, hlam, p2463_0]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [h2342, hc03, hlam, hphi, ht0b, ht45, ht5b, p2463_1, u4ehi3]
                                · have p2463_0 := h2463c.1
                                  have p2463_1 := h2463c.2.1
                                  have p2463_2 := h2463c.2.2.1
                                  have p2463_3 := h2463c.2.2.2
                                  linarith only [hlam, p2463_0]
                          · linarith only [h1, h2342, h2355, h2364, hlam]
                        · linarith only [h1, h2316, h2355, h2359, h2363, hlam]
                    · linarith only [h1, h2316, h2360, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                  · linarith only [h1, h2316, h2359, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2546 | h2546
            · linarith only [h1, h2316, h2342, h2546, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2548 | h2548
              · linarith only [h0, h1, h2342, h2548, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2550 | h2550
                · linarith only [h0, h1, h2319, h2342, h2550, hc02, hc35, hlam, hphi, ht23]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2552 | h2552
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2553 | h2553
                    · linarith only [h1, h2316, h2342, h2552, h2553, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h1, h2316, h2552, h2553, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                  · linarith only [h1, h2316, h2552, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
        · linarith only [h1, h2316, h2341, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2558 | h2558
    · linarith only [h0, h1, h2558, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2560 | h2560
      · linarith only [h0, h2316, h2560, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2562 | h2562
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2563 | h2563
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2564 | h2564
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2565 | h2565
              · linarith only [h0, h2316, h2558, h2565, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2567 | h2567
                · linarith only [h0, h2316, h2560, h2567, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2569 | h2569
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2570 | h2570
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2571 | h2571
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2572 | h2572
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2573 | h2573
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2574 | h2574
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2575 | h2575
                              · rcases h3bigk with h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c | h2576c
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h1, hlam, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2558, hlam, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2575, hc03, hlam, hphi, ht0b, ht45, ht5b, p2576_1, u4ehi4]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  rcases p2576_3 (m.d 0 3) (by simp) with h2581 | h2581
                                  · rcases p2576_3 (m.d 1 3) (by simp) with h2582 | h2582
                                    · rcases p2576_3 (m.d 2 3) (by simp) with h2583 | h2583
                                      · rcases p2576_3 (m.d 3 4) (by simp) with h2584 | h2584
                                        · linarith only [h2562, h2584, hlam]
                                        · linarith only [h2575, h2584, hlam]
                                      · linarith only [h2573, h2583, hlam]
                                    · linarith only [h2570, h2582, hlam]
                                  · linarith only [h2581, hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h0, h1, h2565, hc12, hc23, hlam, hphi, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2565, hlam, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2565, h2575, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2576_1, u4ehi4]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  rcases p2576_3 (m.d 0 3) (by simp) with h2594 | h2594
                                  · linarith only [h1, h2594, hlam]
                                  · linarith only [h2563, h2594, hlam]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2562, h2575, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2576_1, u4ehi4]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h0, h1, hc12, hc23, hlam, hphi, p2576_1]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2575, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2576_1, u4ehi4]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  rcases p2576_3 (m.d 0 3) (by simp) with h2601 | h2601
                                  · linarith only [h2558, h2601, hlam]
                                  · linarith only [h2563, h2601, hlam]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2562, hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2569, hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2572, hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2562, h2575, hc03, hlam, hphi, ht0b, ht45, ht5b, p2576_1, u4ehi4]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2563, hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2570, hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2573, hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [h2575, hlam, p2576_0]
                                · have p2576_0 := h2576c.1
                                  have p2576_1 := h2576c.2.1
                                  have p2576_2 := h2576c.2.2.1
                                  have p2576_3 := h2576c.2.2.2
                                  linarith only [hlam, p2576_0]
                              · rcases h3bigk with h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c | h2614c
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h1, hlam, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2558, hlam, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  rcases p2614_3 (m.d 0 3) (by simp) with h2618 | h2618
                                  · rcases p2614_3 (m.d 1 3) (by simp) with h2619 | h2619
                                    · rcases p2614_3 (m.d 2 3) (by simp) with h2620 | h2620
                                      · rcases p2614_3 (m.d 3 4) (by simp) with h2621 | h2621
                                        · linarith only [h2621, hlam, p2614_0]
                                        · rcases p2614_3 (m.d 3 5) (by simp) with h2623 | h2623
                                          · linarith only [h2563, h2623, hlam]
                                          · linarith only [h2575, h2623, hlam]
                                      · linarith only [h2572, h2620, hlam]
                                    · linarith only [h2569, h2619, hlam]
                                  · linarith only [h2618, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  rcases p2614_3 (m.d 0 3) (by simp) with h2629 | h2629
                                  · rcases p2614_3 (m.d 1 3) (by simp) with h2630 | h2630
                                    · rcases p2614_3 (m.d 2 3) (by simp) with h2631 | h2631
                                      · rcases p2614_3 (m.d 3 4) (by simp) with h2632 | h2632
                                        · linarith only [h2562, h2632, hlam]
                                        · rcases p2614_3 (m.d 3 5) (by simp) with h2634 | h2634
                                          · linarith only [h2634, hlam, p2614_0]
                                          · rcases h4bigk with h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2316, hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2560, hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              rcases p2636_3 (m.d 0 4) (by simp) with h2640 | h2640
                                              · rcases p2636_3 (m.d 1 4) (by simp) with h2641 | h2641
                                                · rcases p2636_3 (m.d 2 4) (by simp) with h2642 | h2642
                                                  · rcases p2636_3 (m.d 3 4) (by simp) with h2643 | h2643
                                                    · linarith only [h2562, h2643, hlam]
                                                    · rcases p2636_3 (m.d 4 5) (by simp) with h2645 | h2645
                                                      · linarith only [h2564, h2645, hlam]
                                                      · linarith only [h2575, h2645, hlam]
                                                  · linarith only [h2572, h2642, hlam]
                                                · linarith only [h2569, h2641, hlam]
                                              · linarith only [h2562, h2640, hlam]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2316, h2565, h2569, h2575, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2636_1, u4ehi3]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h0, h2316, h2565, h2569, hc12, hc23, hlam, hphi, p2636_1]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2567, hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              rcases p2636_3 (m.d 0 4) (by simp) with h2655 | h2655
                                              · linarith only [h2316, h2655, hlam]
                                              · linarith only [h2562, h2655, hlam]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2565, h2569, h2575, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2636_1, u4ehi3]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2564, h2572, h2575, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2636_1, u4ehi3]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h0, h2316, h2572, hc12, hc23, hlam, hphi, p2636_1]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              rcases p2636_3 (m.d 0 4) (by simp) with h2662 | h2662
                                              · linarith only [h2560, h2662, hlam]
                                              · linarith only [h2562, h2662, hlam]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2572, h2575, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2636_1, u4ehi3]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2562, hlam, p2636_1]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2569, hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2572, hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2575, hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2564, hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2571, hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2574, hlam, p2636_0]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [h2564, hc04, hlam, hphi, ht0b, ht45, ht5b, p2636_1, u4ehi3]
                                            · have p2636_0 := h2636c.1
                                              have p2636_1 := h2636c.2.1
                                              have p2636_2 := h2636c.2.2.1
                                              have p2636_3 := h2636c.2.2.2
                                              linarith only [hlam, p2636_0]
                                      · linarith only [h2573, h2631, hlam]
                                    · linarith only [h2570, h2630, hlam]
                                  · linarith only [h2629, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h0, h1, h2565, hc12, hc23, hlam, hphi, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2565, hlam, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  rcases p2614_3 (m.d 0 3) (by simp) with h2682 | h2682
                                  · linarith only [h1, h2682, hlam]
                                  · linarith only [h2562, h2682, hlam]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  rcases p2614_3 (m.d 0 3) (by simp) with h2685 | h2685
                                  · linarith only [h1, h2685, hlam]
                                  · linarith only [h2563, h2685, hlam]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2562, h2564, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2614_1, u4ehi4]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h0, h1, hc12, hc23, hlam, hphi, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  rcases p2614_3 (m.d 0 3) (by simp) with h2691 | h2691
                                  · linarith only [h2558, h2691, hlam]
                                  · linarith only [h2562, h2691, hlam]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  rcases p2614_3 (m.d 0 3) (by simp) with h2694 | h2694
                                  · linarith only [h2558, h2694, hlam]
                                  · linarith only [h2563, h2694, hlam]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2562, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2569, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2572, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2575, hlam, p2614_1]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2563, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2570, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2573, hlam, p2614_0]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [h2563, hc03, hlam, hphi, ht0b, ht45, ht5b, p2614_1, u4ehi3]
                                · have p2614_0 := h2614c.1
                                  have p2614_1 := h2614c.2.1
                                  have p2614_2 := h2614c.2.2.1
                                  have p2614_3 := h2614c.2.2.2
                                  linarith only [hlam, p2614_0]
                            · linarith only [h0, h2316, h2564, h2567, h2574, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h1, h2563, h2565, h2573, hlam]
                        · linarith only [h0, h1, h2565, h2572, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h2316, h2562, h2564, h2571, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1, h2563, h2570, hlam]
                  · linarith only [h1, h2562, h2569, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2713 | h2713
              · linarith only [h0, h2316, h2564, h2713, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2715 | h2715
                · linarith only [h0, h2316, h2564, h2715, hc45, hlam, hphi, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2717 | h2717
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2718 | h2718
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2719 | h2719
                      · linarith only [h0, h2316, h2564, h2715, h2719, hc12, hc24, hlam, hphi]
                      · linarith only [h0, h2316, h2719, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h1, h2563, h2718, hlam]
                  · linarith only [h0, h1, h2717, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2724 | h2724
            · linarith only [h2562, h2563, h2724, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2726 | h2726
              · linarith only [h0, h1, h2563, h2726, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2728 | h2728
                · linarith only [h0, h2316, h2724, h2728, hc45, hlam, hphi, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2730 | h2730
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2731 | h2731
                    · linarith only [h0, h2316, h2562, h2563, h2726, h2731, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h2731, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h1, h2562, h2730, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2735 | h2735
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2736 | h2736
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2737 | h2737
              · linarith only [h0, h2558, h2737, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2739 | h2739
                · linarith only [h0, h1, h2562, h2739, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2741 | h2741
                  · linarith only [h0, h1, h2562, h2737, h2741, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h2741, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h2562, h2735, h2736, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2745 | h2745
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2746 | h2746
              · linarith only [h0, h1, h2735, h2746, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2748 | h2748
                · linarith only [h0, h1, h2735, h2748, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2750 | h2750
                  · linarith only [h0, h1, h2562, h2746, h2750, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h2750, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2753 | h2753
              · linarith only [h0, h1, h2735, h2753, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2755 | h2755
                · linarith only [h0, h1, h2562, h2745, h2755, hc45, hlam, hphi, u4ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2757 | h2757
                  · linarith only [h0, h1, h2562, h2753, h2757, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h2757, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5518000 in
set_option maxHeartbeats 5518000 in
theorem r1l7_13_24_L_I_M_IR_s0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_13_24_L_I_M_IR_s0_x0 m hb3 hb4 hg0 h1
  · exact r1l7_13_24_L_I_M_IR_s0_x1 m hb3 hb4 hg0 h1

end R2N4
