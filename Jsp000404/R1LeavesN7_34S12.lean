import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2086 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2336 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2407 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2408 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h2409 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  rcases m.htr 2 3 4 (by decide) (by decide) with h2410 | h2410
  · rcases m.htr 2 3 5 (by decide) (by decide) with h2411 | h2411
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2412 | h2412
      · rcases m.htr 3 4 5 (by decide) (by decide) with h2413 | h2413
        · rcases h1bigk with h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c | h2414c
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            rcases p2414_3 (m.d 0 1) (by simp) with h2416 | h2416
            · rcases p2414_3 (m.d 1 2) (by simp) with h2417 | h2417
              · linarith only [h2417, hlam, p2414_0]
              · rcases p2414_3 (m.d 1 3) (by simp) with h2419 | h2419
                · linarith only [h1, h2419, hlam]
                · linarith only [h2419, h9, hlam]
            · linarith only [h2416, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [h2407, h2413, hc01, hc45, hlam, hphi, ht0b, ht5b, p2414_1]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            rcases p2414_3 (m.d 0 1) (by simp) with h2424 | h2424
            · rcases p2414_3 (m.d 1 2) (by simp) with h2425 | h2425
              · linarith only [h0, h2425, hlam]
              · rcases p2414_3 (m.d 1 3) (by simp) with h2427 | h2427
                · linarith only [h1, h2427, hlam]
                · linarith only [h2407, h2427, hlam]
            · linarith only [h2424, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            rcases p2414_3 (m.d 0 1) (by simp) with h2431 | h2431
            · rcases p2414_3 (m.d 1 2) (by simp) with h2432 | h2432
              · linarith only [h0, h2432, hlam]
              · rcases p2414_3 (m.d 1 3) (by simp) with h2434 | h2434
                · linarith only [h1, h2434, hlam]
                · linarith only [h2408, h2434, hlam]
            · linarith only [h2431, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [h0, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [h9, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [h2086, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [h2336, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [h1, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            rcases p2414_3 (m.d 0 1) (by simp) with h2444 | h2444
            · rcases p2414_3 (m.d 1 2) (by simp) with h2445 | h2445
              · linarith only [h2445, h9, hlam]
              · rcases p2414_3 (m.d 1 3) (by simp) with h2447 | h2447
                · rcases p2414_3 (m.d 1 4) (by simp) with h2448 | h2448
                  · linarith only [h2407, h2448, hlam]
                  · linarith only [h2086, h2448, hlam]
                · linarith only [h2447, h9, hlam]
            · linarith only [h0, h2444, hlam]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [h0, h2407, h2413, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p2414_1]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            rcases p2414_3 (m.d 0 1) (by simp) with h2455 | h2455
            · rcases p2414_3 (m.d 1 2) (by simp) with h2456 | h2456
              · linarith only [h2456, h9, hlam]
              · rcases p2414_3 (m.d 1 3) (by simp) with h2458 | h2458
                · rcases p2414_3 (m.d 1 4) (by simp) with h2459 | h2459
                  · linarith only [h2407, h2459, hlam]
                  · linarith only [h2409, h2459, hlam]
                · linarith only [h2408, h2458, hlam]
            · linarith only [h2455, h3, hlam]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [h2, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            rcases p2414_3 (m.d 0 1) (by simp) with h2465 | h2465
            · rcases p2414_3 (m.d 1 2) (by simp) with h2466 | h2466
              · linarith only [h2086, h2466, hlam]
              · rcases p2414_3 (m.d 1 3) (by simp) with h2468 | h2468
                · rcases p2414_3 (m.d 1 4) (by simp) with h2469 | h2469
                  · rcases p2414_3 (m.d 1 5) (by simp) with h2470 | h2470
                    · linarith only [h2409, h2470, hlam]
                    · linarith only [h2336, h2470, hlam]
                  · linarith only [h2086, h2469, hlam]
                · linarith only [h2468, h9, hlam]
            · linarith only [h0, h2465, hlam]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [h2407, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            rcases p2414_3 (m.d 0 1) (by simp) with h2478 | h2478
            · rcases p2414_3 (m.d 1 2) (by simp) with h2479 | h2479
              · linarith only [h2086, h2479, hlam]
              · rcases p2414_3 (m.d 1 3) (by simp) with h2481 | h2481
                · rcases p2414_3 (m.d 1 4) (by simp) with h2482 | h2482
                  · rcases p2414_3 (m.d 1 5) (by simp) with h2483 | h2483
                    · linarith only [h2409, h2483, hlam]
                    · rcases h3bigk with h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h0, h2407, h2413, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2485_1]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h0, h2086, h2410, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p2414_1, p2485_1]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        rcases p2485_3 (m.d 0 3) (by simp) with h2489 | h2489
                        · rcases p2485_3 (m.d 1 3) (by simp) with h2490 | h2490
                          · linarith only [h1, h2490, hlam]
                          · linarith only [h2407, h2490, hlam]
                        · linarith only [h2489, hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        rcases p2485_3 (m.d 0 3) (by simp) with h2494 | h2494
                        · rcases p2485_3 (m.d 1 3) (by simp) with h2495 | h2495
                          · linarith only [h1, h2495, hlam]
                          · linarith only [h2408, h2495, hlam]
                        · linarith only [h2494, hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h1, hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h9, hlam, p2485_1]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h1, h2413, hc01, hc45, hlam, hphi, ht0b, ht5b, p2485_1]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        rcases p2485_3 (m.d 0 3) (by simp) with h2503 | h2503
                        · rcases p2485_3 (m.d 1 3) (by simp) with h2504 | h2504
                          · rcases p2485_3 (m.d 2 3) (by simp) with h2505 | h2505
                            · rcases p2485_3 (m.d 3 4) (by simp) with h2506 | h2506
                              · linarith only [h2407, h2506, hlam]
                              · linarith only [h2413, h2506, hlam]
                            · linarith only [h2411, h2505, hlam]
                          · linarith only [h2504, hlam, p2485_0]
                        · linarith only [h2503, h7, hlam]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h4, hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h2407, h2413, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2485_1]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h0, h2413, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2485_1]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        rcases p2485_3 (m.d 0 3) (by simp) with h2516 | h2516
                        · rcases p2485_3 (m.d 1 3) (by simp) with h2517 | h2517
                          · linarith only [h2517, h9, hlam]
                          · linarith only [h2408, h2517, hlam]
                        · linarith only [h2516, h7, hlam]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h6, hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h2407, hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h2410, hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h0, h2407, h4, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p2485_1]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h7, hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h2408, hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h2411, hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [h2413, hlam, p2485_0]
                      · have p2485_0 := h2485c.1
                        have p2485_1 := h2485c.2.1
                        have p2485_2 := h2485c.2.2.1
                        have p2485_3 := h2485c.2.2.2
                        linarith only [hlam, p2485_0]
                  · linarith only [h2409, h2482, hlam]
                · linarith only [h2408, h2481, hlam]
            · linarith only [h2478, h3, hlam]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [h3, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            rcases p2414_3 (m.d 0 1) (by simp) with h2535 | h2535
            · rcases p2414_3 (m.d 1 2) (by simp) with h2536 | h2536
              · linarith only [h2336, h2536, hlam]
              · rcases p2414_3 (m.d 1 3) (by simp) with h2538 | h2538
                · rcases p2414_3 (m.d 1 4) (by simp) with h2539 | h2539
                  · rcases p2414_3 (m.d 1 5) (by simp) with h2540 | h2540
                    · rcases h3bigk with h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h0, h2408, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2414_1, p2541_1]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h0, h2336, h2410, h2412, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2414_1, p2541_1]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        rcases p2541_3 (m.d 0 3) (by simp) with h2545 | h2545
                        · rcases p2541_3 (m.d 1 3) (by simp) with h2546 | h2546
                          · linarith only [h1, h2546, hlam]
                          · linarith only [h2407, h2546, hlam]
                        · linarith only [h2545, hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        rcases p2541_3 (m.d 0 3) (by simp) with h2550 | h2550
                        · rcases p2541_3 (m.d 1 3) (by simp) with h2551 | h2551
                          · linarith only [h1, h2551, hlam]
                          · linarith only [h2408, h2551, hlam]
                        · linarith only [h2550, hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h1, hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h9, hlam, p2541_1]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h1, h2413, hc01, hc45, hlam, hphi, ht0b, ht5b, p2541_1]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        rcases p2541_3 (m.d 0 3) (by simp) with h2559 | h2559
                        · rcases p2541_3 (m.d 1 3) (by simp) with h2560 | h2560
                          · rcases p2541_3 (m.d 2 3) (by simp) with h2561 | h2561
                            · rcases p2541_3 (m.d 3 4) (by simp) with h2562 | h2562
                              · linarith only [h2407, h2562, hlam]
                              · linarith only [h2413, h2562, hlam]
                            · linarith only [h2411, h2561, hlam]
                          · linarith only [h2560, hlam, p2541_0]
                        · linarith only [h2559, h7, hlam]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h4, hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h0, h2407, h2413, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2541_1]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h0, h2413, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2541_1]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        rcases p2541_3 (m.d 0 3) (by simp) with h2572 | h2572
                        · rcases p2541_3 (m.d 1 3) (by simp) with h2573 | h2573
                          · linarith only [h2573, h9, hlam]
                          · linarith only [h2408, h2573, hlam]
                        · linarith only [h2572, h7, hlam]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h6, hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h2407, hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h2410, hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h1, h2407, h2413, hc01, hc45, hlam, hphi, ht0b, ht5b, p2541_1]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h7, hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h2408, hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h2411, hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [h2413, hlam, p2541_0]
                      · have p2541_0 := h2541c.1
                        have p2541_1 := h2541c.2.1
                        have p2541_2 := h2541c.2.2.1
                        have p2541_3 := h2541c.2.2.2
                        linarith only [hlam, p2541_0]
                    · linarith only [h2336, h2540, hlam]
                  · linarith only [h2086, h2539, hlam]
                · linarith only [h2538, h9, hlam]
            · linarith only [h0, h2535, hlam]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [h2408, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [h2409, hlam, p2414_0]
          · have p2414_0 := h2414c.1
            have p2414_1 := h2414c.2.1
            have p2414_2 := h2414c.2.2.1
            have p2414_3 := h2414c.2.2.2
            linarith only [hlam, p2414_0]
        · rcases h1bigk with h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            rcases p2594_3 (m.d 0 1) (by simp) with h2596 | h2596
            · rcases p2594_3 (m.d 1 2) (by simp) with h2597 | h2597
              · linarith only [h2597, hlam, p2594_0]
              · rcases p2594_3 (m.d 1 3) (by simp) with h2599 | h2599
                · linarith only [h1, h2599, hlam]
                · linarith only [h2599, h9, hlam]
            · linarith only [h2596, hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h2407, h2409, h2413, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2594_1]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h2409, h2413, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2594_1]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            rcases p2594_3 (m.d 0 1) (by simp) with h2605 | h2605
            · rcases p2594_3 (m.d 1 2) (by simp) with h2606 | h2606
              · linarith only [h0, h2606, hlam]
              · rcases p2594_3 (m.d 1 3) (by simp) with h2608 | h2608
                · linarith only [h1, h2608, hlam]
                · linarith only [h2408, h2608, hlam]
            · linarith only [h2605, hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h0, hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h9, hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h2086, hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h2336, hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h1, hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            rcases p2594_3 (m.d 0 1) (by simp) with h2618 | h2618
            · rcases p2594_3 (m.d 1 2) (by simp) with h2619 | h2619
              · linarith only [h2619, h9, hlam]
              · rcases p2594_3 (m.d 1 3) (by simp) with h2621 | h2621
                · rcases p2594_3 (m.d 1 4) (by simp) with h2622 | h2622
                  · linarith only [h2407, h2622, hlam]
                  · linarith only [h2086, h2622, hlam]
                · linarith only [h2621, h9, hlam]
            · linarith only [h0, h2618, hlam]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h2409, h2413, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2594_1]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h0, h2409, h2413, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2594_1]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h2, hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            rcases p2594_3 (m.d 0 1) (by simp) with h2631 | h2631
            · rcases p2594_3 (m.d 1 2) (by simp) with h2632 | h2632
              · linarith only [h2086, h2632, hlam]
              · rcases p2594_3 (m.d 1 3) (by simp) with h2634 | h2634
                · rcases p2594_3 (m.d 1 4) (by simp) with h2635 | h2635
                  · rcases p2594_3 (m.d 1 5) (by simp) with h2636 | h2636
                    · linarith only [h2409, h2636, hlam]
                    · linarith only [h2336, h2636, hlam]
                  · linarith only [h2086, h2635, hlam]
                · linarith only [h2634, h9, hlam]
            · linarith only [h0, h2631, hlam]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h2407, hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h2, h2409, h2413, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2594_1]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h3, hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            rcases p2594_3 (m.d 0 1) (by simp) with h2646 | h2646
            · rcases p2594_3 (m.d 1 2) (by simp) with h2647 | h2647
              · linarith only [h2336, h2647, hlam]
              · rcases p2594_3 (m.d 1 3) (by simp) with h2649 | h2649
                · rcases p2594_3 (m.d 1 4) (by simp) with h2650 | h2650
                  · rcases p2594_3 (m.d 1 5) (by simp) with h2651 | h2651
                    · rcases h3bigk with h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c | h2652c
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h0, h2408, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2594_1, p2652_1]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h0, h2336, h2410, h2412, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2594_1, p2652_1]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2656 | h2656
                        · rcases p2652_3 (m.d 1 3) (by simp) with h2657 | h2657
                          · linarith only [h1, h2657, hlam]
                          · linarith only [h2407, h2657, hlam]
                        · linarith only [h2656, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2661 | h2661
                        · rcases p2652_3 (m.d 1 3) (by simp) with h2662 | h2662
                          · linarith only [h1, h2662, hlam]
                          · linarith only [h2408, h2662, hlam]
                        · linarith only [h2661, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h1, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h9, hlam, p2652_1]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2669 | h2669
                        · rcases p2652_3 (m.d 1 3) (by simp) with h2670 | h2670
                          · rcases p2652_3 (m.d 2 3) (by simp) with h2671 | h2671
                            · rcases p2652_3 (m.d 3 4) (by simp) with h2672 | h2672
                              · linarith only [h2672, hlam, p2652_0]
                              · rcases p2652_3 (m.d 3 5) (by simp) with h2674 | h2674
                                · linarith only [h2408, h2674, hlam]
                                · linarith only [h2413, h2674, hlam]
                            · linarith only [h2410, h2671, hlam]
                          · linarith only [h2670, hlam, p2652_0]
                        · linarith only [h2669, h6, hlam]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2680 | h2680
                        · rcases p2652_3 (m.d 1 3) (by simp) with h2681 | h2681
                          · rcases p2652_3 (m.d 2 3) (by simp) with h2682 | h2682
                            · rcases p2652_3 (m.d 3 4) (by simp) with h2683 | h2683
                              · linarith only [h2407, h2683, hlam]
                              · rcases p2652_3 (m.d 3 5) (by simp) with h2685 | h2685
                                · linarith only [h2685, hlam, p2652_0]
                                · rcases h4bigk with h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c | h2687c
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2409, h2413, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h0, h2086, h2409, h2413, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    rcases p2687_3 (m.d 0 4) (by simp) with h2691 | h2691
                                    · rcases p2687_3 (m.d 1 4) (by simp) with h2692 | h2692
                                      · linarith only [h2, h2692, hlam]
                                      · linarith only [h2407, h2692, hlam]
                                    · linarith only [h2691, h6, hlam]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    rcases p2687_3 (m.d 0 4) (by simp) with h2696 | h2696
                                    · rcases p2687_3 (m.d 1 4) (by simp) with h2697 | h2697
                                      · linarith only [h2, h2697, hlam]
                                      · linarith only [h2409, h2697, hlam]
                                    · linarith only [h2696, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2, hlam, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2086, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    rcases p2687_3 (m.d 0 4) (by simp) with h2704 | h2704
                                    · rcases p2687_3 (m.d 1 4) (by simp) with h2705 | h2705
                                      · rcases p2687_3 (m.d 2 4) (by simp) with h2706 | h2706
                                        · rcases p2687_3 (m.d 3 4) (by simp) with h2707 | h2707
                                          · linarith only [h2407, h2707, hlam]
                                          · rcases p2687_3 (m.d 4 5) (by simp) with h2709 | h2709
                                            · linarith only [h2409, h2709, hlam]
                                            · linarith only [h2413, h2709, hlam]
                                        · linarith only [h2410, h2706, hlam]
                                      · linarith only [h2407, h2705, hlam]
                                    · linarith only [h2704, h6, hlam]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2, h2413, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h5, hlam, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h0, h2409, h2413, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    rcases p2687_3 (m.d 0 4) (by simp) with h2719 | h2719
                                    · rcases p2687_3 (m.d 1 4) (by simp) with h2720 | h2720
                                      · linarith only [h2086, h2720, hlam]
                                      · linarith only [h2407, h2720, hlam]
                                    · linarith only [h2719, h6, hlam]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h0, h2410, h2413, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h6, hlam, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2407, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2410, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2413, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h8, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2409, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2412, hlam, p2687_0]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [h2, h2409, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2687_1]
                                  · have p2687_0 := h2687c.1
                                    have p2687_1 := h2687c.2.1
                                    have p2687_2 := h2687c.2.2.1
                                    have p2687_3 := h2687c.2.2.2
                                    linarith only [hlam, p2687_0]
                            · linarith only [h2411, h2682, hlam]
                          · linarith only [h2681, hlam, p2652_0]
                        · linarith only [h2680, h7, hlam]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h4, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h0, h2407, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2652_1]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2741 | h2741
                        · rcases p2652_3 (m.d 1 3) (by simp) with h2742 | h2742
                          · linarith only [h2742, h9, hlam]
                          · linarith only [h2407, h2742, hlam]
                        · linarith only [h2741, h6, hlam]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        rcases p2652_3 (m.d 0 3) (by simp) with h2746 | h2746
                        · rcases p2652_3 (m.d 1 3) (by simp) with h2747 | h2747
                          · linarith only [h2747, h9, hlam]
                          · linarith only [h2408, h2747, hlam]
                        · linarith only [h2746, h7, hlam]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h6, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2407, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2410, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2413, hlam, p2652_1]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h7, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2408, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h2411, hlam, p2652_0]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [h1, h2408, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2652_1]
                      · have p2652_0 := h2652c.1
                        have p2652_1 := h2652c.2.1
                        have p2652_2 := h2652c.2.2.1
                        have p2652_3 := h2652c.2.2.2
                        linarith only [hlam, p2652_0]
                    · linarith only [h2336, h2651, hlam]
                  · linarith only [h2086, h2650, hlam]
                · linarith only [h2649, h9, hlam]
            · linarith only [h0, h2646, hlam]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h2408, hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [h2409, hlam, p2594_0]
          · have p2594_0 := h2594c.1
            have p2594_1 := h2594c.2.1
            have p2594_2 := h2594c.2.2.1
            have p2594_3 := h2594c.2.2.2
            linarith only [hlam, p2594_0]
      · linarith only [h2086, h2409, h2412, hlam]
    · linarith only [h2408, h2411, h9, hlam]
  · linarith only [h2407, h2410, h9, hlam]

end R2N4
