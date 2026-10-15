import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_48S0
import Jsp000404.R1LeavesN7_48S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1117 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1118 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1119 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1120 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h2371 | h2371
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2372 | h2372
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2373 | h2373
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2374 | h2374
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2375 | h2375
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2376 | h2376
            · linarith only [h1120, h2371, h2376, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2378 | h2378
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2379 | h2379
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2380 | h2380
                  · linarith only [h1117, h1120, h2371, h2380, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2382 | h2382
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2383 | h2383
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2384 | h2384
                        · rcases h0bigk with h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [hlam, p2385_0]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h0, hlam, p2385_1]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h692, hlam, p2385_0]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h921, hlam, p2385_1]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h1036, hlam, p2385_1]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            rcases p2385_3 (m.d 0 1) (by simp) with h2391 | h2391
                            · linarith only [h0, h2391, hlam]
                            · rcases p2385_3 (m.d 0 2) (by simp) with h2393 | h2393
                              · rcases p2385_3 (m.d 0 3) (by simp) with h2394 | h2394
                                · linarith only [h1117, h2394, hlam]
                                · linarith only [h2394, h692, hlam]
                              · linarith only [h0, h2393, hlam]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [hlam, p2385_0]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h0, h1117, h2382, h2384, hc12, hlam, hphi, ht01, ht0b, ht5b, p2385_1, u5ehi4]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h0, h1117, h1120, h2382, h2384, hc12, hlam, hphi, ht01, ht0b, ht5b, p2385_1, u5ehi4]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            rcases p2385_3 (m.d 0 1) (by simp) with h2401 | h2401
                            · linarith only [h0, h2401, hlam]
                            · rcases p2385_3 (m.d 0 2) (by simp) with h2403 | h2403
                              · rcases p2385_3 (m.d 0 3) (by simp) with h2404 | h2404
                                · linarith only [h1117, h2404, hlam]
                                · linarith only [h2371, h2404, hlam]
                              · linarith only [h1119, h2403, hlam]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h2376, h692, hc01, hc34, hlam, hphi, ht12, ht23, p2385_1]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h1117, hlam, p2385_1]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [hlam, p2385_0]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h1120, hlam, p2385_1]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h1119, h2376, h692, hc34, hlam, hphi, ht23, p2385_1, u2ehi4]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            rcases p2385_3 (m.d 0 1) (by simp) with h2413 | h2413
                            · linarith only [h2413, h921, hlam]
                            · rcases p2385_3 (m.d 0 2) (by simp) with h2415 | h2415
                              · rcases p2385_3 (m.d 0 3) (by simp) with h2416 | h2416
                                · linarith only [h1120, h2416, hlam]
                                · linarith only [h2416, h692, hlam]
                              · linarith only [h0, h2415, hlam]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h1118, hlam, p2385_0]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h1117, h2382, h2384, hc04, hlam, hphi, ht0b, ht5b, p2385_1, u5ehi4]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [hlam, p2385_0]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h1119, h1120, hc34, hlam, hphi, ht23, p2385_1, u2ehi4]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h1036, h2376, h2378, hc01, hc34, hlam, hphi, ht12, ht23, p2385_1]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h1119, hlam, p2385_1]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h2371, hlam, p2385_0]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [h2372, hlam, p2385_1]
                          · have p2385_0 := h2385c.1
                            have p2385_1 := h2385c.2.1
                            have p2385_2 := h2385c.2.2.1
                            have p2385_3 := h2385c.2.2.2
                            linarith only [hlam, p2385_0]
                        · linarith only [h1117, h2376, h2382, h2384, h692, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                      · linarith only [h1036, h2372, h2376, h2378, h2383, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h2371, h2376, h2382, h692, hc23, hc34, hlam, hphi]
                · linarith only [h1036, h2372, h2376, h2378, h2379, h921, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h2371, h2378, h692, hlam]
          · linarith only [h0, h1117, h2375, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h1117, h2374, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h1118, h2373, hc23, hlam, hphi, u2ehi3]
    · linarith only [h1120, h2371, h2372, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2438 | h2438
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2439 | h2439
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2440 | h2440
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2441 | h2441
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2442 | h2442
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2443 | h2443
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2444 | h2444
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2445 | h2445
                  · linarith only [h1117, h1120, h2445, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2447 | h2447
                    · linarith only [h1117, h2371, h2447, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2449 | h2449
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2450 | h2450
                        · rcases h0bigk with h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c | h2451c
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [hlam, p2451_0]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h0, hlam, p2451_1]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h692, hlam, p2451_0]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h921, hlam, p2451_1]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h1036, hlam, p2451_1]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            rcases p2451_3 (m.d 0 1) (by simp) with h2457 | h2457
                            · linarith only [h0, h2457, hlam]
                            · rcases p2451_3 (m.d 0 2) (by simp) with h2459 | h2459
                              · rcases p2451_3 (m.d 0 3) (by simp) with h2460 | h2460
                                · linarith only [h1117, h2460, hlam]
                                · linarith only [h2460, h692, hlam]
                              · linarith only [h0, h2459, hlam]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [hlam, p2451_0]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            rcases p2451_3 (m.d 0 1) (by simp) with h2465 | h2465
                            · linarith only [h0, h2465, hlam]
                            · rcases p2451_3 (m.d 0 2) (by simp) with h2467 | h2467
                              · rcases p2451_3 (m.d 0 3) (by simp) with h2468 | h2468
                                · linarith only [h1117, h2468, hlam]
                                · rcases p2451_3 (m.d 0 4) (by simp) with h2470 | h2470
                                  · linarith only [h1118, h2470, hlam]
                                  · linarith only [h1120, h2470, hlam]
                              · linarith only [h1117, h2467, hlam]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h0, h1118, h2449, hc12, hlam, hphi, ht01, ht0b, ht5b, p2451_1, u5ehi4]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            rcases p2451_3 (m.d 0 1) (by simp) with h2475 | h2475
                            · linarith only [h0, h2475, hlam]
                            · rcases p2451_3 (m.d 0 2) (by simp) with h2477 | h2477
                              · rcases p2451_3 (m.d 0 3) (by simp) with h2478 | h2478
                                · linarith only [h1117, h2478, hlam]
                                · rcases p2451_3 (m.d 0 4) (by simp) with h2480 | h2480
                                  · linarith only [h1118, h2480, hlam]
                                  · linarith only [h2438, h2480, hlam]
                              · linarith only [h1119, h2477, hlam]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h2371, h2442, h2450, hc01, hc13, hlam, hphi, p2451_1]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h1117, hlam, p2451_1]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [hlam, p2451_0]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h1120, hlam, p2451_1]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h2371, hlam, p2451_1]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h1120, h2442, hc01, hc13, hlam, hphi, p2451_1]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h1118, hlam, p2451_0]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h1117, h1120, h2442, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2451_1, u2ehi2]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [hlam, p2451_0]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h1120, h2442, hc13, hlam, hphi, ht01, ht0b, ht5b, p2451_1, u5ehi0]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h2371, h2442, h2450, hc01, hc13, hlam, hphi, p2451_1]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h1119, hlam, p2451_1]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h1117, h2371, h2442, h2450, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2451_1, u2ehi2]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [h2438, hlam, p2451_1]
                          · have p2451_0 := h2451c.1
                            have p2451_1 := h2451c.2.1
                            have p2451_2 := h2451c.2.2.1
                            have p2451_3 := h2451c.2.2.2
                            linarith only [hlam, p2451_0]
                        · linarith only [h1118, h1120, h2438, h2449, h2450, hc02, hlam, hphi, ht0b, ht5b, u5ehi0]
                      · linarith only [h1120, h2438, h2449, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h1117, h1120, h2442, h2444, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h1118, h1120, h2442, h2443, hc35, hlam, hphi, ht23, u2ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2503 | h2503
              · linarith only [h1117, h2371, h2442, h2503, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2505 | h2505
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2506 | h2506
                  · linarith only [h1117, h2442, h2506, h692, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2508 | h2508
                    · linarith only [h1117, h2503, h2508, h692, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2510 | h2510
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2511 | h2511
                        · rcases h0bigk with h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [hlam, p2512_0]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h0, hlam, p2512_1]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h692, hlam, p2512_0]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h921, hlam, p2512_1]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h1036, hlam, p2512_1]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            rcases p2512_3 (m.d 0 1) (by simp) with h2518 | h2518
                            · linarith only [h0, h2518, hlam]
                            · rcases p2512_3 (m.d 0 2) (by simp) with h2520 | h2520
                              · rcases p2512_3 (m.d 0 3) (by simp) with h2521 | h2521
                                · linarith only [h1117, h2521, hlam]
                                · linarith only [h2521, h692, hlam]
                              · linarith only [h0, h2520, hlam]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [hlam, p2512_0]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            rcases p2512_3 (m.d 0 1) (by simp) with h2526 | h2526
                            · linarith only [h0, h2526, hlam]
                            · rcases p2512_3 (m.d 0 2) (by simp) with h2528 | h2528
                              · rcases p2512_3 (m.d 0 3) (by simp) with h2529 | h2529
                                · linarith only [h1117, h2529, hlam]
                                · rcases p2512_3 (m.d 0 4) (by simp) with h2531 | h2531
                                  · linarith only [h1118, h2531, hlam]
                                  · linarith only [h1120, h2531, hlam]
                              · linarith only [h1117, h2528, hlam]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h0, h1118, h2510, hc12, hlam, hphi, ht01, ht0b, ht5b, p2512_1, u5ehi4]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            rcases p2512_3 (m.d 0 1) (by simp) with h2536 | h2536
                            · linarith only [h0, h2536, hlam]
                            · rcases p2512_3 (m.d 0 2) (by simp) with h2538 | h2538
                              · rcases p2512_3 (m.d 0 3) (by simp) with h2539 | h2539
                                · linarith only [h1117, h2539, hlam]
                                · rcases p2512_3 (m.d 0 4) (by simp) with h2541 | h2541
                                  · linarith only [h1118, h2541, hlam]
                                  · linarith only [h2438, h2541, hlam]
                              · linarith only [h1119, h2538, hlam]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h2503, h2511, h692, hc01, hc34, hlam, hphi, ht12, ht23, p2512_1]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h1117, hlam, p2512_1]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [hlam, p2512_0]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h1120, hlam, p2512_1]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h2371, hlam, p2512_1]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            rcases p2512_3 (m.d 0 1) (by simp) with h2550 | h2550
                            · linarith only [h2550, h921, hlam]
                            · rcases p2512_3 (m.d 0 2) (by simp) with h2552 | h2552
                              · rcases p2512_3 (m.d 0 3) (by simp) with h2553 | h2553
                                · linarith only [h1120, h2553, hlam]
                                · linarith only [h2553, h692, hlam]
                              · linarith only [h0, h2552, hlam]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h1118, hlam, p2512_0]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h1117, h2442, h921, hc34, hlam, hphi, ht23, p2512_1, u2ehi2]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [hlam, p2512_0]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h1117, h2371, h2442, h921, hc34, hlam, hphi, ht23, p2512_1, u2ehi2]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            rcases p2512_3 (m.d 0 1) (by simp) with h2561 | h2561
                            · linarith only [h1036, h2561, hlam]
                            · rcases p2512_3 (m.d 0 2) (by simp) with h2563 | h2563
                              · rcases p2512_3 (m.d 0 3) (by simp) with h2564 | h2564
                                · linarith only [h2371, h2564, hlam]
                                · linarith only [h2564, h692, hlam]
                              · linarith only [h0, h2563, hlam]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h1119, hlam, p2512_1]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h1036, h1117, h2503, hc35, hlam, hphi, ht23, p2512_1, u2ehi2]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [h2438, hlam, p2512_1]
                          · have p2512_0 := h2512c.1
                            have p2512_1 := h2512c.2.1
                            have p2512_2 := h2512c.2.2.1
                            have p2512_3 := h2512c.2.2.2
                            linarith only [hlam, p2512_0]
                        · linarith only [h2442, h2510, h2511, h921, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h1120, h2438, h2510, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h2438, h2505, h921, hlam]
          · linarith only [h0, h1117, h2441, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h1119, h2440, hc24, hlam, hphi, u2ehi4]
      · linarith only [h0, h1119, h2439, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2578 | h2578
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2579 | h2579
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2580 | h2580
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2581 | h2581
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2582 | h2582
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2583 | h2583
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2584 | h2584
                  · linarith only [h1117, h1120, h2584, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2586 | h2586
                    · linarith only [h1117, h1120, h2438, h2578, h2581, h2583, h2586, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2588 | h2588
                      · linarith only [h1118, h2438, h2588, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2590 | h2590
                        · linarith only [h1117, h1120, h2438, h2590, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h1117, h1120, h2578, h2581, h2583, h2590, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h1117, h1120, h2581, h2583, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h1117, h1120, h2581, h2582, hc35, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2595 | h2595
              · linarith only [h1117, h2371, h2581, h2595, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2597 | h2597
                · linarith only [h1118, h2438, h2581, h2597, hc34, hlam, hphi, ht23, u2ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2599 | h2599
                  · linarith only [h1117, h1120, h2599, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2601 | h2601
                    · linarith only [h1036, h1117, h2581, h2595, h2601, h692, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2603 | h2603
                      · linarith only [h2581, h2597, h2603, h692, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2605 | h2605
                        · linarith only [h1118, h2597, h2605, h921, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h1117, h1120, h2605, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h0, h1117, h2580, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h1118, h2579, hlam]
      · linarith only [h0, h1117, h2578, hlam]

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1117 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1118 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1119 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h1120 | h1120
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036 h1117 h1118 h1119 h1120
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036 h1117 h1118 h1119 h1120

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1117 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1118 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1119 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
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
  linarith only [h1117, h1119, hc25, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1117 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1118 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h1119 | h1119
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036 h1117 h1118 h1119
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036 h1117 h1118 h1119

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1117 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1118 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
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
  linarith only [h1117, h1118, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1117 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h1118 | h1118
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036 h1117 h1118
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036 h1117 h1118

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1117 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h2613 | h2613
  · linarith only [h1117, h2613, hc23, hlam, hphi, u2ehi3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2615 | h2615
    · linarith only [h1117, h2615, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2617 | h2617
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2618 | h2618
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2619 | h2619
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2620 | h2620
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2621 | h2621
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2622 | h2622
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2623 | h2623
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2624 | h2624
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2625 | h2625
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2626 | h2626
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2627 | h2627
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2628 | h2628
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2629 | h2629
                              · linarith only [h1117, h2617, h2620, h2629, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · rcases h0bigk with h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c | h2631c
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [hlam, p2631_0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h0, hlam, p2631_1]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h692, hlam, p2631_0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h921, hlam, p2631_1]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h1036, hlam, p2631_1]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h2615, h2620, h2626, h2628, hc01, hc12, hlam, hphi, p2631_1]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [hlam, p2631_0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h1117, hlam, p2631_0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h2613, hlam, p2631_1]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h2615, hlam, p2631_0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h1117, h2620, hc01, hc12, hlam, hphi, p2631_1]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h1117, h2620, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2631_1, u2ehi0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [hlam, p2631_0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h1117, h2619, h2620, h2629, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2631_1]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h1117, h2615, h2620, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2631_1, u2ehi0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h2613, h2620, h2626, hc01, hc12, hlam, hphi, p2631_1]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h2613, h2620, h2626, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2631_1, u2ehi0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h2617, hlam, p2631_0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [hlam, p2631_0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h2613, h2615, h2620, h2626, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2631_1, u2ehi0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h2615, h2620, h2626, h2628, hc01, hc12, hlam, hphi, p2631_1]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h2615, h2620, h2626, h2628, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2631_1, u2ehi0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h2618, hlam, p2631_0]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [h2619, hlam, p2631_1]
                                · have p2631_0 := h2631c.1
                                  have p2631_1 := h2631c.2.1
                                  have p2631_2 := h2631c.2.2.1
                                  have p2631_3 := h2631c.2.2.2
                                  linarith only [hlam, p2631_0]
                            · linarith only [h2613, h2628, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h1117, h2627, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1117, h2626, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2613, h2617, h2619, h2621, h2625, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h1117, h2613, h2618, h2620, h2621, h2623, h2624, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h1117, h2617, h2620, h2623, hlam]
                · linarith only [h1117, h2618, h2620, h2622, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h1117, h2620, h2621, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2665 | h2665
              · linarith only [h2620, h2665, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2667 | h2667
                · linarith only [h2620, h2667, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2669 | h2669
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2670 | h2670
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2671 | h2671
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2672 | h2672
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2673 | h2673
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2674 | h2674
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2675 | h2675
                              · rcases h0bigk with h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c | h2676c
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [hlam, p2676_0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h0, hlam, p2676_1]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h692, hlam, p2676_0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h921, hlam, p2676_1]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h1036, hlam, p2676_1]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h0, h2667, h2672, h2674, hc01, hc23, hlam, hphi, ht12, p2676_1]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [hlam, p2676_0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h1117, hlam, p2676_0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h2613, hlam, p2676_1]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h2615, hlam, p2676_0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  rcases p2676_3 (m.d 0 1) (by simp) with h2687 | h2687
                                  · linarith only [h2687, h692, hlam]
                                  · rcases p2676_3 (m.d 0 2) (by simp) with h2689 | h2689
                                    · linarith only [h1117, h2689, hlam]
                                    · linarith only [h0, h2689, hlam]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h2620, h692, hc23, hlam, hphi, p2676_1, u2ehi0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [hlam, p2676_0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h2615, h2619, h2620, h692, hc23, hlam, hphi, p2676_1, u2ehi0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h2615, h2620, h692, hc23, hlam, hphi, p2676_1, u2ehi0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  rcases p2676_3 (m.d 0 1) (by simp) with h2696 | h2696
                                  · linarith only [h2696, h921, hlam]
                                  · rcases p2676_3 (m.d 0 2) (by simp) with h2698 | h2698
                                    · linarith only [h2613, h2698, hlam]
                                    · linarith only [h0, h2698, hlam]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h2613, h2672, hc23, hlam, hphi, p2676_1, u2ehi0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h2617, hlam, p2676_0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [hlam, p2676_0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h2615, h2617, h2620, h692, hc23, hlam, hphi, p2676_1, u2ehi0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  rcases p2676_3 (m.d 0 1) (by simp) with h2705 | h2705
                                  · linarith only [h1036, h2705, hlam]
                                  · rcases p2676_3 (m.d 0 2) (by simp) with h2707 | h2707
                                    · linarith only [h2615, h2707, hlam]
                                    · linarith only [h0, h2707, hlam]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h2615, h2672, h2674, hc23, hlam, hphi, p2676_1, u2ehi0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h2618, hlam, p2676_0]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [h2619, hlam, p2676_1]
                                · have p2676_0 := h2676c.1
                                  have p2676_1 := h2676c.2.1
                                  have p2676_2 := h2676c.2.2.1
                                  have p2676_3 := h2676c.2.2.2
                                  linarith only [hlam, p2676_0]
                              · rcases h0bigk with h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c | h2714c
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [hlam, p2714_0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h0, hlam, p2714_1]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h692, hlam, p2714_0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h921, hlam, p2714_1]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h1036, hlam, p2714_1]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h0, h2667, h2672, h2674, hc01, hc23, hlam, hphi, ht12, p2714_1]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [hlam, p2714_0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h1117, hlam, p2714_0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h2613, hlam, p2714_1]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h2615, hlam, p2714_0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  rcases p2714_3 (m.d 0 1) (by simp) with h2725 | h2725
                                  · linarith only [h2725, h692, hlam]
                                  · rcases p2714_3 (m.d 0 2) (by simp) with h2727 | h2727
                                    · linarith only [h1117, h2727, hlam]
                                    · linarith only [h0, h2727, hlam]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h2620, h692, hc23, hlam, hphi, p2714_1, u2ehi0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [hlam, p2714_0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h2619, h2620, h692, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2714_1, u5ehi4]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h2615, h2620, h692, hc23, hlam, hphi, p2714_1, u2ehi0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  rcases p2714_3 (m.d 0 1) (by simp) with h2734 | h2734
                                  · linarith only [h2734, h921, hlam]
                                  · rcases p2714_3 (m.d 0 2) (by simp) with h2736 | h2736
                                    · linarith only [h2613, h2736, hlam]
                                    · linarith only [h0, h2736, hlam]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h2665, h2672, h921, hc23, hlam, hphi, p2714_1, u2ehi0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h2617, hlam, p2714_0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [hlam, p2714_0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h2615, h2665, h2672, h921, hc23, hlam, hphi, p2714_1, u2ehi0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  rcases p2714_3 (m.d 0 1) (by simp) with h2743 | h2743
                                  · linarith only [h1036, h2743, hlam]
                                  · rcases p2714_3 (m.d 0 2) (by simp) with h2745 | h2745
                                    · linarith only [h2615, h2745, hlam]
                                    · linarith only [h0, h2745, hlam]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h1036, h2667, h2672, h2674, hc23, hlam, hphi, p2714_1, u2ehi0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h2618, hlam, p2714_0]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [h2619, hlam, p2714_1]
                                · have p2714_0 := h2714c.1
                                  have p2714_1 := h2714c.2.1
                                  have p2714_2 := h2714c.2.2.1
                                  have p2714_3 := h2714c.2.2.2
                                  linarith only [hlam, p2714_0]
                            · linarith only [h2613, h2674, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h0, h2665, h2672, h2673, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h1117, h2672, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2617, h2619, h2671, h692, h921, hc01, hc13, hlam, hphi]
                    · linarith only [h2618, h2670, h692, hlam]
                  · linarith only [h2617, h2669, h692, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2758 | h2758
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2759 | h2759
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2760 | h2760
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2761 | h2761
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2762 | h2762
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2763 | h2763
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2764 | h2764
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2765 | h2765
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2766 | h2766
                            · linarith only [h2613, h2619, h2766, hc24, hlam, hphi, u2ehi0]
                            · linarith only [h2613, h2758, h2761, h2763, h2766, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1117, h2618, h2765, hlam]
                        · linarith only [h1117, h2617, h2618, h2619, h2758, h2761, h2763, h2764, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h2613, h2759, h2763, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h2618, h2762, h692, hlam]
                  · linarith only [h1117, h2617, h2758, h2761, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h1117, h2618, h2758, h2760, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h1117, h2758, h2759, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2776 | h2776
              · linarith only [h2758, h2776, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2778 | h2778
                · linarith only [h2758, h2778, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2780 | h2780
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2781 | h2781
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2782 | h2782
                      · linarith only [h2613, h2619, h2776, h2782, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2784 | h2784
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2785 | h2785
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2786 | h2786
                            · linarith only [h2776, h2782, h2784, h2786, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h2613, h2786, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h2618, h2758, h2785, h692, hlam]
                        · linarith only [h1117, h2784, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h2618, h2781, h692, hlam]
                  · linarith only [h2617, h2780, h692, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2793 | h2793
          · linarith only [h2617, h2618, h2793, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2795 | h2795
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2796 | h2796
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2797 | h2797
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2798 | h2798
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2799 | h2799
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2800 | h2800
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2801 | h2801
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2802 | h2802
                          · linarith only [h2617, h2618, h2795, h2802, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1117, h2802, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1117, h2801, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2613, h2796, h2800, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h1117, h2795, h2799, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1117, h2617, h2795, h2798, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h2795, h2797, hc25, hlam, hphi, u2ehi2]
              · linarith only [h1117, h2795, h2796, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2811 | h2811
              · linarith only [h2795, h2811, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2813 | h2813
                · linarith only [h2795, h2813, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2815 | h2815
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2816 | h2816
                    · linarith only [h1117, h2618, h2795, h2816, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2818 | h2818
                      · linarith only [h2613, h2793, h2815, h2816, h2818, hc35, hlam, hphi, ht23, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2820 | h2820
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2821 | h2821
                          · linarith only [h2811, h2815, h2816, h2821, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h1117, h2821, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h0, h2617, h2795, h2820, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h2617, h2618, h2815, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2826 | h2826
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2827 | h2827
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2828 | h2828
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2829 | h2829
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2830 | h2830
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2831 | h2831
                  · linarith only [h2617, h2826, h2831, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h1117, h2828, h2831, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h2829, h2830, hc25, hlam, hphi, u2ehi3]
              · linarith only [h1117, h2828, h2829, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2836 | h2836
              · linarith only [h2828, h2836, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2838 | h2838
                · linarith only [h2828, h2838, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2840 | h2840
                  · linarith only [h2617, h2826, h2828, h2840, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2842 | h2842
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2843 | h2843
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2844 | h2844
                        · linarith only [h2838, h2840, h2842, h2844, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1117, h2844, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2826, h2827, h2840, h2843, h692, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h2826, h2842, h692, hlam]
          · linarith only [h2617, h2826, h2827, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2850 | h2850
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2851 | h2851
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2852 | h2852
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2853 | h2853
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2854 | h2854
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2855 | h2855
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2856 | h2856
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2857 | h2857
                        · linarith only [h1117, h2617, h2857, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1117, h2851, h2854, h2857, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h2850, h2856, h921, hlam]
                    · linarith only [h2617, h2854, h2855, hc03, hc35, hlam, hphi]
                  · linarith only [h1117, h2851, h2854, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h2613, h2852, h2853, hc25, hlam, hphi, u2ehi0]
              · linarith only [h1117, h2851, h2852, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2865 | h2865
              · linarith only [h2851, h2865, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2867 | h2867
                · linarith only [h2851, h2867, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2869 | h2869
                  · linarith only [h1117, h2617, h2851, h2869, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2871 | h2871
                    · linarith only [h1117, h2826, h2869, h2871, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2873 | h2873
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2874 | h2874
                        · linarith only [h2851, h2869, h2874, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1117, h2874, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2850, h2873, h921, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2878 | h2878
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2879 | h2879
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2880 | h2880
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2881 | h2881
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2882 | h2882
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2883 | h2883
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2884 | h2884
                        · linarith only [h1117, h2617, h2878, h2884, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h1117, h2884, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h2613, h2879, h2883, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h1117, h2878, h2882, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1117, h2878, h2881, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1117, h2878, h2880, hc25, hlam, hphi, u2ehi0]
              · linarith only [h1117, h2878, h2879, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2892 | h2892
              · linarith only [h2878, h2892, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2894 | h2894
                · linarith only [h2878, h2894, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2896 | h2896
                  · linarith only [h1117, h2617, h2878, h2896, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2898 | h2898
                    · linarith only [h1117, h2826, h2896, h2898, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2900 | h2900
                      · linarith only [h2613, h2850, h2892, h2900, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2902 | h2902
                        · linarith only [h1117, h2617, h2902, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1117, h2902, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h1117 | h1117
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036 h1117
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036 h1117

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h1036 | h1036
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h921 | h921
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h692 h921
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h692 h921

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h692 | h692
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x0 m hb0 hb2 hb3 hb5 h0 h692
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1 m hb0 hb2 hb3 hb5 h0 h692

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
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
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
