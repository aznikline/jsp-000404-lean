import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_50S3
import Jsp000404.R1LeavesN7_50S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h999 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1080 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2346 | h2346
  · linarith only [h1080, h2346, hc23, hlam, hphi, u2ehi3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2348 | h2348
    · linarith only [h1080, h2348, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2350 | h2350
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2351 | h2351
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2352 | h2352
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2353 | h2353
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2354 | h2354
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2355 | h2355
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2356 | h2356
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2357 | h2357
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2358 | h2358
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2359 | h2359
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2360 | h2360
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2361 | h2361
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2362 | h2362
                              · linarith only [h1080, h2350, h2353, h2362, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases h1bigk with h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h0, hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h655, hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h884, hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h999, hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  rcases p2364_3 (m.d 0 1) (by simp) with h2370 | h2370
                                  · linarith only [h2370, hlam, p2364_0]
                                  · rcases p2364_3 (m.d 1 2) (by simp) with h2372 | h2372
                                    · rcases p2364_3 (m.d 1 3) (by simp) with h2373 | h2373
                                      · linarith only [h2353, h2373, hlam]
                                      · linarith only [h2373, h655, hlam]
                                    · linarith only [h2372, hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h2348, h2353, h2359, h2361, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2364_1, u2ehi0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h2348, h2355, h2358, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2364_1, u2ehi0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h2348, h2355, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2364_1, u2ehi0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  rcases p2364_3 (m.d 0 1) (by simp) with h2381 | h2381
                                  · linarith only [h2381, hlam, p2364_0]
                                  · rcases p2364_3 (m.d 1 2) (by simp) with h2383 | h2383
                                    · rcases p2364_3 (m.d 1 3) (by simp) with h2384 | h2384
                                      · rcases p2364_3 (m.d 1 4) (by simp) with h2385 | h2385
                                        · linarith only [h2356, h2385, hlam]
                                        · linarith only [h2385, h884, hlam]
                                      · linarith only [h2384, hlam, p2364_0]
                                    · linarith only [h0, h2383, hlam]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h2353, hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h2348, h2355, h2358, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2364_1, u2ehi0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h2348, h2353, h2355, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2364_1, u2ehi0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  rcases p2364_3 (m.d 0 1) (by simp) with h2394 | h2394
                                  · linarith only [h2394, hlam, p2364_0]
                                  · rcases p2364_3 (m.d 1 2) (by simp) with h2396 | h2396
                                    · rcases p2364_3 (m.d 1 3) (by simp) with h2397 | h2397
                                      · rcases p2364_3 (m.d 1 4) (by simp) with h2398 | h2398
                                        · rcases p2364_3 (m.d 1 5) (by simp) with h2399 | h2399
                                          · linarith only [h2358, h2399, hlam]
                                          · linarith only [h2399, h999, hlam]
                                        · linarith only [h2398, hlam, p2364_0]
                                      · linarith only [h2397, h655, hlam]
                                    · linarith only [h0, h2396, hlam]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h2354, hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h2356, hlam, p2364_1]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h2348, h2355, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2364_1, u2ehi0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  rcases p2364_3 (m.d 0 1) (by simp) with h2409 | h2409
                                  · linarith only [h2409, hlam, p2364_0]
                                  · rcases p2364_3 (m.d 1 2) (by simp) with h2411 | h2411
                                    · rcases p2364_3 (m.d 1 3) (by simp) with h2412 | h2412
                                      · rcases p2364_3 (m.d 1 4) (by simp) with h2413 | h2413
                                        · rcases p2364_3 (m.d 1 5) (by simp) with h2414 | h2414
                                          · rcases h4bigk with h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c | h2415c
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [hlam, p2415_0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h884, hlam, p2415_1]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2346, hlam, p2415_1]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              rcases p2415_3 (m.d 0 4) (by simp) with h2419 | h2419
                                              · rcases p2415_3 (m.d 1 4) (by simp) with h2420 | h2420
                                                · rcases p2415_3 (m.d 2 4) (by simp) with h2421 | h2421
                                                  · rcases p2415_3 (m.d 3 4) (by simp) with h2422 | h2422
                                                    · linarith only [h2350, h2422, hlam]
                                                    · rcases p2415_3 (m.d 4 5) (by simp) with h2424 | h2424
                                                      · linarith only [h2352, h2424, hlam]
                                                      · linarith only [h2362, h2424, hlam]
                                                  · linarith only [h2359, h2421, hlam]
                                                · linarith only [h2356, h2420, hlam]
                                              · linarith only [h2350, h2419, hlam]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2346, h2353, h2359, h2362, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2415_1]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2352, h2353, h2356, h2362, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2415_1]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [hlam, p2415_0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2346, h2353, h2356, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2415_1, u2ehi0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              rcases p2415_3 (m.d 0 4) (by simp) with h2434 | h2434
                                              · linarith only [h2434, h884, hlam]
                                              · linarith only [h2350, h2434, hlam]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              rcases p2415_3 (m.d 0 4) (by simp) with h2437 | h2437
                                              · linarith only [h2437, h884, hlam]
                                              · linarith only [h2352, h2437, hlam]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2352, h2359, h2362, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2415_1]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2354, hlam, p2415_0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [hlam, p2415_0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              rcases p2415_3 (m.d 0 4) (by simp) with h2443 | h2443
                                              · linarith only [h2346, h2443, hlam]
                                              · linarith only [h2350, h2443, hlam]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2353, h2359, h2362, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2415_1]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2350, hlam, p2415_0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2356, hlam, p2415_0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2359, hlam, p2415_0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [hlam, p2415_0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2362, hlam, p2415_0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2352, hlam, p2415_0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2358, hlam, p2415_0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2361, hlam, p2415_0]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [h2346, h2352, h2353, h2359, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2415_1]
                                            · have p2415_0 := h2415c.1
                                              have p2415_1 := h2415c.2.1
                                              have p2415_2 := h2415c.2.2.1
                                              have p2415_3 := h2415c.2.2.2
                                              linarith only [hlam, p2415_0]
                                          · linarith only [h2414, hlam, p2364_0]
                                        · linarith only [h2413, h884, hlam]
                                      · linarith only [h2412, h655, hlam]
                                    · linarith only [h0, h2411, hlam]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h2355, hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h2357, hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [h2358, hlam, p2364_0]
                                · have p2364_0 := h2364c.1
                                  have p2364_1 := h2364c.2.1
                                  have p2364_2 := h2364c.2.2.1
                                  have p2364_3 := h2364c.2.2.2
                                  linarith only [hlam, p2364_0]
                            · linarith only [h2346, h2352, h2361, hlam]
                          · linarith only [h1080, h2360, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1080, h2359, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2352, h2358, h884, hlam]
                    · linarith only [h1080, h2351, h2357, h655, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h1080, h2350, h2353, h2356, hlam]
                · linarith only [h1080, h2351, h2353, h2355, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h1080, h2353, h2354, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2473 | h2473
              · linarith only [h2353, h2473, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2475 | h2475
                · linarith only [h2353, h2475, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2477 | h2477
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2478 | h2478
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2479 | h2479
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2480 | h2480
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2481 | h2481
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2482 | h2482
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2483 | h2483
                              · rcases h1bigk with h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c | h2484c
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [hlam, p2484_0]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h0, hlam, p2484_0]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h655, hlam, p2484_0]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h884, hlam, p2484_0]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h999, hlam, p2484_0]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h2475, h2480, h2482, hc01, hc23, hlam, hphi, ht12, p2484_1]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [hlam, p2484_0]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h2353, hlam, p2484_1]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h2473, hlam, p2484_1]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h2475, hlam, p2484_1]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  rcases p2484_3 (m.d 0 1) (by simp) with h2495 | h2495
                                  · linarith only [h2495, hlam, p2484_0]
                                  · rcases p2484_3 (m.d 1 2) (by simp) with h2497 | h2497
                                    · linarith only [h2353, h2497, hlam]
                                    · linarith only [h0, h2497, hlam]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h2353, hc23, hlam, hphi, p2484_1, u2ehi1]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [hlam, p2484_0]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h2353, h884, hc01, hc23, hlam, hphi, ht12, p2484_1]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h2353, h999, hc01, hc23, hlam, hphi, ht12, p2484_1]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  rcases p2484_3 (m.d 0 1) (by simp) with h2504 | h2504
                                  · linarith only [h2504, hlam, p2484_0]
                                  · rcases p2484_3 (m.d 1 2) (by simp) with h2506 | h2506
                                    · linarith only [h2473, h2506, hlam]
                                    · linarith only [h0, h2506, hlam]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, p2484_1]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h2477, hlam, p2484_1]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [hlam, p2484_0]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h2348, h2473, h2480, h999, hc23, hlam, hphi, p2484_1, u2ehi0]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  rcases p2484_3 (m.d 0 1) (by simp) with h2513 | h2513
                                  · linarith only [h2513, hlam, p2484_0]
                                  · rcases p2484_3 (m.d 1 2) (by simp) with h2515 | h2515
                                    · linarith only [h2475, h2515, hlam]
                                    · linarith only [h0, h2515, hlam]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h0, hc01, hc15, hlam, hphi, p2484_1]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h2478, hlam, p2484_0]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [h2479, hlam, p2484_0]
                                · have p2484_0 := h2484c.1
                                  have p2484_1 := h2484c.2.1
                                  have p2484_2 := h2484c.2.2.1
                                  have p2484_3 := h2484c.2.2.2
                                  linarith only [hlam, p2484_0]
                              · rcases h1bigk with h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c | h2522c
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [hlam, p2522_0]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h0, hlam, p2522_0]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h655, hlam, p2522_0]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h884, hlam, p2522_0]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h999, hlam, p2522_0]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h2353, hc01, hc23, hlam, hphi, ht12, p2522_1]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [hlam, p2522_0]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h2353, hlam, p2522_1]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h2473, hlam, p2522_1]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h2475, hlam, p2522_1]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  rcases p2522_3 (m.d 0 1) (by simp) with h2533 | h2533
                                  · linarith only [h2533, hlam, p2522_0]
                                  · rcases p2522_3 (m.d 1 2) (by simp) with h2535 | h2535
                                    · linarith only [h2353, h2535, hlam]
                                    · linarith only [h0, h2535, hlam]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h2353, hc23, hlam, hphi, p2522_1, u2ehi1]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [hlam, p2522_0]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h2352, h2353, h2483, h884, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2522_1]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h2353, h999, hc01, hc23, hlam, hphi, ht12, p2522_1]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  rcases p2522_3 (m.d 0 1) (by simp) with h2542 | h2542
                                  · linarith only [h2542, hlam, p2522_0]
                                  · rcases p2522_3 (m.d 1 2) (by simp) with h2544 | h2544
                                    · linarith only [h2473, h2544, hlam]
                                    · linarith only [h0, h2544, hlam]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, p2522_1]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h2477, hlam, p2522_1]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [hlam, p2522_0]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h2348, h2473, h2480, h999, hc23, hlam, hphi, p2522_1, u2ehi0]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  rcases p2522_3 (m.d 0 1) (by simp) with h2551 | h2551
                                  · linarith only [h2551, hlam, p2522_0]
                                  · rcases p2522_3 (m.d 1 2) (by simp) with h2553 | h2553
                                    · linarith only [h2475, h2553, hlam]
                                    · linarith only [h0, h2553, hlam]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h0, hc01, hc15, hlam, hphi, p2522_1]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h2478, hlam, p2522_0]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [h2479, hlam, p2522_0]
                                · have p2522_0 := h2522c.1
                                  have p2522_1 := h2522c.2.1
                                  have p2522_2 := h2522c.2.2.1
                                  have p2522_3 := h2522c.2.2.2
                                  linarith only [hlam, p2522_0]
                            · linarith only [h2350, h2352, h2353, h2482, h655, hc23, hlam, hphi, u2ehi3]
                          · linarith only [h1080, h2481, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h0, h2353, h2480, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h2350, h2352, h2479, h655, h884, hc01, hc13, hlam, hphi]
                    · linarith only [h2351, h2478, h655, hlam]
                  · linarith only [h2350, h2477, h655, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2566 | h2566
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2567 | h2567
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2568 | h2568
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2569 | h2569
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2570 | h2570
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2571 | h2571
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2572 | h2572
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2573 | h2573
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2574 | h2574
                            · linarith only [h2346, h2352, h2566, h2572, h2574, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · linarith only [h2346, h2569, h2571, h2574, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1080, h2351, h2573, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h1080, h2572, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2346, h2567, h2571, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h1080, h2351, h2566, h2570, h655, hc01, hc12, hlam, hphi]
                  · linarith only [h1080, h2350, h2566, h2569, hlam]
                · linarith only [h1080, h2351, h2566, h2568, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h1080, h2566, h2567, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2584 | h2584
              · linarith only [h2566, h2584, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2586 | h2586
                · linarith only [h2566, h2586, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2588 | h2588
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2589 | h2589
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2590 | h2590
                      · linarith only [h2346, h2352, h2584, h2590, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2592 | h2592
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2593 | h2593
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2594 | h2594
                            · linarith only [h2584, h2590, h2592, h2594, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h2346, h2594, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h2351, h2566, h2593, h655, hlam]
                        · linarith only [h1080, h2592, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h2351, h2589, h655, hlam]
                  · linarith only [h2350, h2588, h655, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2601 | h2601
          · linarith only [h2350, h2351, h2601, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2603 | h2603
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2604 | h2604
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2605 | h2605
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2606 | h2606
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2607 | h2607
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2608 | h2608
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2609 | h2609
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2610 | h2610
                          · linarith only [h2350, h2351, h2603, h2610, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1080, h2610, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1080, h2609, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2346, h2604, h2608, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h1080, h2603, h2607, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1080, h2350, h2603, h2606, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h2603, h2605, hc25, hlam, hphi, u2ehi2]
              · linarith only [h1080, h2603, h2604, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2619 | h2619
              · linarith only [h2603, h2619, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2621 | h2621
                · linarith only [h2603, h2621, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2623 | h2623
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2624 | h2624
                    · linarith only [h1080, h2351, h2603, h2624, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2626 | h2626
                      · linarith only [h2346, h2601, h2623, h2624, h2626, hc35, hlam, hphi, ht23, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2628 | h2628
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2629 | h2629
                          · linarith only [h2619, h2623, h2624, h2629, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h1080, h2629, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h0, h2350, h2603, h2628, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h2350, h2351, h2623, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2634 | h2634
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2635 | h2635
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2636 | h2636
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2637 | h2637
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2638 | h2638
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2639 | h2639
                  · linarith only [h2350, h2634, h2639, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h1080, h2636, h2639, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h2637, h2638, hc25, hlam, hphi, u2ehi3]
              · linarith only [h1080, h2636, h2637, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2644 | h2644
              · linarith only [h2636, h2644, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2646 | h2646
                · linarith only [h2636, h2646, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2648 | h2648
                  · linarith only [h2350, h2634, h2636, h2648, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2650 | h2650
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2651 | h2651
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2652 | h2652
                        · linarith only [h2646, h2648, h2650, h2652, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1080, h2652, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2634, h2635, h2648, h2651, h655, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h2634, h2650, h655, hlam]
          · linarith only [h2350, h2634, h2635, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2658 | h2658
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2659 | h2659
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2660 | h2660
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2661 | h2661
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2662 | h2662
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2663 | h2663
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2664 | h2664
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2665 | h2665
                        · linarith only [h1080, h2350, h2659, h2665, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h1080, h2665, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2658, h2664, h884, hlam]
                    · linarith only [h2346, h2350, h2662, h2663, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1080, h2659, h2662, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1080, h2659, h2661, hc25, hlam, hphi, u2ehi0]
              · linarith only [h1080, h2659, h2660, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2673 | h2673
              · linarith only [h2659, h2673, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2675 | h2675
                · linarith only [h2659, h2675, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2677 | h2677
                  · linarith only [h1080, h2350, h2659, h2677, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2679 | h2679
                    · linarith only [h1080, h2634, h2677, h2679, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2681 | h2681
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2682 | h2682
                        · linarith only [h2659, h2677, h2682, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1080, h2682, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2658, h2681, h884, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2686 | h2686
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2687 | h2687
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2688 | h2688
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2689 | h2689
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2690 | h2690
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2691 | h2691
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2692 | h2692
                        · linarith only [h1080, h2350, h2686, h2692, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h1080, h2692, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2346, h2687, h2691, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h1080, h2350, h2689, h2690, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1080, h2686, h2689, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1080, h2686, h2688, hc25, hlam, hphi, u2ehi0]
              · linarith only [h1080, h2686, h2687, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2700 | h2700
              · linarith only [h2686, h2700, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2702 | h2702
                · linarith only [h2686, h2702, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2704 | h2704
                  · linarith only [h1080, h2350, h2686, h2704, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2706 | h2706
                    · linarith only [h1080, h2634, h2704, h2706, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2708 | h2708
                      · linarith only [h1080, h2350, h2658, h2700, h2708, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2710 | h2710
                        · linarith only [h1080, h2350, h2710, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1080, h2710, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h999 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1080 | h1080
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 h0 h655 h884 h999 h1080
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 h0 h655 h884 h999 h1080

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h999 | h999
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 h0 h655 h884 h999
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 h0 h655 h884 h999

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h884 | h884
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x0 m hb1 hb2 hb4 hb5 h0 h655 h884
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1 m hb1 hb2 hb4 hb5 h0 h655 h884

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h655 | h655
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x0 m hb1 hb2 hb4 hb5 h0 h655
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1 m hb1 hb2 hb4 hb5 h0 h655

set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1 m hb1 hb2 hb4 hb5 h0

end R2N4
