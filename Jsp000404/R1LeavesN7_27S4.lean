import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_27S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h2417 | h2417
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2418 | h2418
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2419 | h2419
      · linarith only [h0, h2, h2419, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2421 | h2421
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2422 | h2422
          · linarith only [h0, h2, h2418, h2422, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2424 | h2424
            · linarith only [h2422, h2424, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2426 | h2426
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2427 | h2427
                · linarith only [h0, h2, h2427, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h2418, h2419, h2427, hc12, hc24, hlam, hphi]
              · linarith only [h0, h2, h2418, h2426, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2431 | h2431
          · linarith only [h2, h2417, h2418, h2421, h2431, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2433 | h2433
            · linarith only [h2431, h2433, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2435 | h2435
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2436 | h2436
                · linarith only [h0, h2, h2436, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h2418, h2421, h2436, hc12, hc25, hlam, hphi]
              · linarith only [h2, h2417, h2418, h2421, h2435, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2440 | h2440
      · linarith only [h0, h2, h2440, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2442 | h2442
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2443 | h2443
          · linarith only [h1, h2, h2443, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2445 | h2445
            · linarith only [h2443, h2445, hc34, hlam, hphi, u3ehi4]
            · linarith only [h2418, h2442, h2445, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2448 | h2448
          · linarith only [h1, h2, h2448, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2450 | h2450
            · linarith only [h2448, h2450, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2452 | h2452
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2453 | h2453
                · linarith only [h0, h2, h2453, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2455 | h2455
                  · linarith only [h1, h2, h2440, h2453, h2455, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2457 | h2457
                    · linarith only [h0, h2, h2442, h2455, h2457, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2459 | h2459
                      · linarith only [h1, h2, h2448, h2455, h2459, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h1, h2, h2459, hc34, hlam, hphi, u3ehi1]
              · linarith only [h1, h2, h2452, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2463 | h2463
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2464 | h2464
      · linarith only [h0, h2, h2464, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2466 | h2466
        · linarith only [h0, h2417, h2466, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2468 | h2468
          · linarith only [h0, h2, h2463, h2468, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2470 | h2470
            · linarith only [h2468, h2470, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2472 | h2472
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2473 | h2473
                · linarith only [h0, h2, h2473, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h2463, h2464, h2473, hc12, hc24, hlam, hphi]
              · linarith only [h1, h2, h2472, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2477 | h2477
      · linarith only [h1, h2, h2463, h2477, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2479 | h2479
        · linarith only [h1, h2417, h2463, h2479, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2481 | h2481
          · linarith only [h1, h2, h2481, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2483 | h2483
            · linarith only [h2481, h2483, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2485 | h2485
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2486 | h2486
                · linarith only [h0, h2, h2463, h2486, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2488 | h2488
                  · linarith only [h0, h2417, h2477, h2485, h2488, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2490 | h2490
                    · linarith only [h1, h2, h2479, h2486, h2488, h2490, hc02, hc24, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2492 | h2492
                      · linarith only [h1, h2, h2481, h2488, h2492, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h1, h2, h2492, hc34, hlam, hphi, u3ehi1]
              · linarith only [h1, h2, h2485, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h1 h2
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h1 h2

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h2496 | h2496
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2497 | h2497
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2498 | h2498
      · linarith only [h0, h1, h2498, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2500 | h2500
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2501 | h2501
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2502 | h2502
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2503 | h2503
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2504 | h2504
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2505 | h2505
                  · linarith only [h2498, h2501, h2505, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2507 | h2507
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2508 | h2508
                      · linarith only [h0, h1, h2505, h2508, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h2501, h2505, h2508, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h2500, h2505, h2507, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2512 | h2512
                  · linarith only [h0, h1, h2512, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2514 | h2514
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2515 | h2515
                      · linarith only [h0, h1, h2512, h2515, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h2501, h2512, h2514, h2515, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1, h2500, h2512, h2514, hc12, hc23, hlam, hphi]
              · linarith only [h2502, h2503, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h2496, h2502, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2521 | h2521
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2522 | h2522
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2523 | h2523
                · linarith only [h2500, h2501, h2523, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2525 | h2525
                  · linarith only [h0, h1, h2525, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2527 | h2527
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2528 | h2528
                      · linarith only [h0, h2501, h2528, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2530 | h2530
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2531 | h2531
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2532 | h2532
                            · linarith only [h1, h2496, h2525, h2532, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2534 | h2534
                              · linarith only [h1, h2497, h2525, h2527, h2528, h2534, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1, h2497, h2525, h2528, h2534, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h2497, h2527, h2528, h2530, h2531, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h2497, h2530, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h2500, h2501, h2527, hc12, hc25, hlam, hphi]
              · linarith only [h2521, h2522, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h2496, h2521, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2542 | h2542
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2543 | h2543
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2544 | h2544
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2545 | h2545
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2546 | h2546
                  · linarith only [h0, h1, h2546, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2548 | h2548
                    · linarith only [h0, h1, h2500, h2542, h2546, h2548, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2550 | h2550
                      · linarith only [h1, h2496, h2546, h2548, h2550, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h2500, h2542, h2550, hc12, hc24, hlam, hphi]
                · linarith only [h2500, h2542, h2545, hlam]
              · linarith only [h2543, h2544, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h2496, h2543, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2556 | h2556
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2557 | h2557
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2558 | h2558
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2559 | h2559
                  · linarith only [h0, h1, h2559, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2561 | h2561
                    · linarith only [h0, h1, h2500, h2559, h2561, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2563 | h2563
                      · linarith only [h0, h1, h2542, h2557, h2559, h2563, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2565 | h2565
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2566 | h2566
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2567 | h2567
                            · linarith only [h1, h2496, h2559, h2567, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h1, h2496, h2558, h2559, h2561, h2567, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h2566, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h2496, h2558, h2565, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2572 | h2572
                  · linarith only [h0, h1, h2572, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2574 | h2574
                    · linarith only [h0, h2500, h2574, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2576 | h2576
                      · linarith only [h0, h2542, h2576, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2578 | h2578
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2579 | h2579
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2580 | h2580
                            · linarith only [h1, h2496, h2558, h2572, h2580, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2582 | h2582
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2583 | h2583
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2584 | h2584
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2585 | h2585
                                    · linarith only [h2496, h2558, h2578, h2585, hlam]
                                    · rcases h0bigk with h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c | h2587c
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h1, h2572, hc02, hc23, hlam, hphi, p2587_1]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h1, hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h1, h2496, h2572, h2578, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2587_1, u3ehi3]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h1, h2572, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2587_1, u5ehi0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h0, hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h2498, hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h2500, hlam, p2587_1]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h2542, hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h1, h2497, h2572, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2587_1, u5ehi1]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        rcases p2587_3 (m.d 0 1) (by simp) with h2599 | h2599
                                        · linarith only [h1, h2599, hlam]
                                        · linarith only [h0, h2599, hlam]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        rcases p2587_3 (m.d 0 1) (by simp) with h2603 | h2603
                                        · linarith only [h1, h2603, hlam]
                                        · linarith only [h2496, h2603, hlam]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        rcases p2587_3 (m.d 0 1) (by simp) with h2606 | h2606
                                        · linarith only [h1, h2606, hlam]
                                        · linarith only [h2497, h2606, hlam]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h2496, hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h0, h2558, h2584, hc12, hc24, hlam, hphi, p2587_1]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h2556, hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h2558, hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h2497, hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h0, h1, h2497, h2572, hc12, hc23, hlam, hphi, p2587_1]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h2557, hlam, p2587_0]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [h1, h2496, h2497, h2572, h2578, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2587_1, u3ehi3]
                                      · have p2587_0 := h2587c.1
                                        have p2587_1 := h2587c.2.1
                                        have p2587_2 := h2587c.2.2.1
                                        have p2587_3 := h2587c.2.2.2
                                        linarith only [hlam, p2587_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2619 | h2619
                                    · linarith only [h1, h2496, h2572, h2578, h2584, h2619, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases h0bigk with h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c | h2621c
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h0, h1, h2572, hc12, hc23, hlam, hphi, p2621_1]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h1, hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h0, h1, h2500, h2572, hc12, hc23, hlam, hphi, p2621_1]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h1, h2572, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2621_1, u5ehi0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h0, hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h2498, hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h2500, hlam, p2621_1]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h2542, hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h1, h2497, h2572, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2621_1, u5ehi1]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        rcases p2621_3 (m.d 0 1) (by simp) with h2633 | h2633
                                        · linarith only [h1, h2633, hlam]
                                        · linarith only [h0, h2633, hlam]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        rcases p2621_3 (m.d 0 1) (by simp) with h2637 | h2637
                                        · linarith only [h1, h2637, hlam]
                                        · linarith only [h2496, h2637, hlam]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        rcases p2621_3 (m.d 0 1) (by simp) with h2640 | h2640
                                        · linarith only [h1, h2640, hlam]
                                        · linarith only [h2497, h2640, hlam]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h2496, hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h0, h1, h2496, h2572, hc12, hc23, hlam, hphi, p2621_1]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h2556, hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h2558, hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h2497, hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h0, h1, h2497, h2572, hc12, hc23, hlam, hphi, p2621_1]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h2557, hlam, p2621_0]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [h1, h2496, h2497, h2572, h2578, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2621_1, u3ehi3]
                                      · have p2621_0 := h2621c.1
                                        have p2621_1 := h2621c.2.1
                                        have p2621_2 := h2621c.2.2.1
                                        have p2621_3 := h2621c.2.2.2
                                        linarith only [hlam, p2621_0]
                                · linarith only [h0, h1, h2572, h2583, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h2497, h2572, h2578, h2580, h2582, hlam]
                          · linarith only [h1, h2497, h2579, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h1, h2497, h2556, h2578, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
              · linarith only [h2556, h2557, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h2496, h2556, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2659 | h2659
      · linarith only [h0, h1, h2659, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2661 | h2661
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2662 | h2662
          · linarith only [h0, h2497, h2662, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2664 | h2664
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2665 | h2665
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2666 | h2666
                · linarith only [h0, h2497, h2661, h2666, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2668 | h2668
                  · linarith only [h0, h1, h2659, h2668, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2670 | h2670
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2671 | h2671
                      · linarith only [h0, h1, h2668, h2671, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2673 | h2673
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2674 | h2674
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2675 | h2675
                            · linarith only [h2496, h2497, h2668, h2674, h2675, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h0, h2497, h2670, h2675, hc24, hc45, hlam, hphi]
                          · linarith only [h0, h1, h2670, h2673, h2674, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h1, h2673, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h2659, h2661, h2670, hc12, hc23, hlam, hphi]
              · linarith only [h2664, h2665, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h2496, h2664, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2683 | h2683
          · linarith only [h2496, h2497, h2661, h2683, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2685 | h2685
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2686 | h2686
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2687 | h2687
                · linarith only [h2496, h2497, h2687, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2689 | h2689
                  · linarith only [h0, h1, h2659, h2689, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2691 | h2691
                    · linarith only [h0, h2661, h2691, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2693 | h2693
                      · linarith only [h0, h2497, h2683, h2693, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2695 | h2695
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2696 | h2696
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2697 | h2697
                            · linarith only [h2496, h2497, h2687, h2697, hlam]
                            · linarith only [h2496, h2497, h2695, h2697, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h1, h2496, h2695, h2696, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h2496, h2691, h2695, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h2685, h2686, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h2496, h2685, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2704 | h2704
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2705 | h2705
      · linarith only [h0, h1, h2705, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2707 | h2707
        · linarith only [h0, h2496, h2707, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2709 | h2709
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2710 | h2710
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2711 | h2711
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2712 | h2712
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2713 | h2713
                  · linarith only [h2705, h2709, h2713, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2715 | h2715
                    · linarith only [h0, h2707, h2709, h2715, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2717 | h2717
                      · linarith only [h0, h1, h2713, h2717, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h2709, h2713, h2717, hc12, hc23, hlam, hphi]
                · linarith only [h2496, h2704, h2712, hlam]
              · linarith only [h2710, h2711, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2722 | h2722
              · linarith only [h2710, h2722, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1, h2709, h2722, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2725 | h2725
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2726 | h2726
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2727 | h2727
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2728 | h2728
                  · linarith only [h0, h1, h2728, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2730 | h2730
                    · linarith only [h0, h1, h2707, h2728, h2730, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2732 | h2732
                      · linarith only [h0, h1, h2709, h2728, h2732, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2734 | h2734
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2735 | h2735
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2736 | h2736
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2737 | h2737
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2738 | h2738
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2739 | h2739
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2740 | h2740
                                    · rcases h0bigk with h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c | h2741c
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [hlam, p2741_0]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h2496, h2728, h2734, hc02, hc23, hlam, hphi, p2741_1]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h1, hlam, p2741_0]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h2496, hlam, p2741_1]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h2496, h2728, h2734, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2741_1, u5ehi0]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h0, hlam, p2741_0]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [hlam, p2741_0]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h2705, hlam, p2741_0]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h2707, hlam, p2741_1]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h2709, hlam, p2741_0]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h2704, hc03, hlam, hphi, ht0b, ht5b, p2741_1, u5ehi1]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        rcases p2741_3 (m.d 0 1) (by simp) with h2753 | h2753
                                        · linarith only [h1, h2753, hlam]
                                        · linarith only [h0, h2753, hlam]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [hlam, p2741_0]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h1, h2496, h2704, h2728, h2735, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2741_1, u3ehi4]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        rcases p2741_3 (m.d 0 1) (by simp) with h2758 | h2758
                                        · linarith only [h1, h2758, hlam]
                                        · linarith only [h2704, h2758, hlam]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h2704, h2735, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p2741_1, u3ehi4]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        rcases p2741_3 (m.d 0 1) (by simp) with h2762 | h2762
                                        · linarith only [h2496, h2762, hlam]
                                        · linarith only [h0, h2762, hlam]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h2725, hlam, p2741_0]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [hlam, p2741_0]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        rcases p2741_3 (m.d 0 1) (by simp) with h2767 | h2767
                                        · linarith only [h2496, h2767, hlam]
                                        · linarith only [h2704, h2767, hlam]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h2704, hlam, p2741_0]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h0, h1, h2704, h2728, hc12, hc23, hlam, hphi, p2741_1]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h2726, hlam, p2741_0]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [h2727, hlam, p2741_1]
                                      · have p2741_0 := h2741c.1
                                        have p2741_1 := h2741c.2.1
                                        have p2741_2 := h2741c.2.2.1
                                        have p2741_3 := h2741c.2.2.2
                                        linarith only [hlam, p2741_0]
                                    · linarith only [h2496, h2704, h2728, h2734, h2736, h2740, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h0, h2496, h2704, h2707, h2728, h2734, h2736, h2739, hc12, hc23, hlam, hphi]
                                · linarith only [h2496, h2704, h2728, h2734, h2738, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                              · linarith only [h2496, h2704, h2725, h2728, h2734, h2735, h2737, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                            · linarith only [h2496, h2704, h2735, h2736, hc45, hlam, hphi, ht34, u3ehi4]
                          · linarith only [h1, h2725, h2735, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h2704, h2734, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                · linarith only [h2496, h2704, h2727, hlam]
              · linarith only [h2725, h2726, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2784 | h2784
              · linarith only [h2725, h2784, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1, h2704, h2784, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2787 | h2787
      · linarith only [h0, h1, h2787, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2789 | h2789
        · linarith only [h0, h2496, h2789, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2791 | h2791
          · linarith only [h0, h2704, h2791, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2793 | h2793
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2794 | h2794
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2795 | h2795
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2796 | h2796
                  · linarith only [h0, h2496, h2787, h2796, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2798 | h2798
                    · linarith only [h0, h2704, h2789, h2795, h2798, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2800 | h2800
                      · linarith only [h0, h2704, h2791, h2800, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2802 | h2802
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2803 | h2803
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2804 | h2804
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2805 | h2805
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2806 | h2806
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2807 | h2807
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2808 | h2808
                                    · rcases h0bigk with h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c | h2809c
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [hlam, p2809_0]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h2704, h2796, h2802, h2804, hc02, hc23, hlam, hphi, p2809_1]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h1, hlam, p2809_0]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h2496, hlam, p2809_1]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h2704, hlam, p2809_1]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h0, hlam, p2809_0]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [hlam, p2809_0]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h2787, hlam, p2809_0]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h2789, hlam, p2809_1]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h2791, hlam, p2809_0]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h0, h1, h2796, hc12, hc23, hlam, hphi, p2809_1]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        rcases p2809_3 (m.d 0 1) (by simp) with h2821 | h2821
                                        · linarith only [h1, h2821, hlam]
                                        · linarith only [h0, h2821, hlam]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [hlam, p2809_0]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h1, h2793, h2796, h2808, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2809_1, u5ehi4]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h0, h1, h2704, h2796, hc12, hc23, hlam, hphi, p2809_1]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h0, h2496, h2796, h2802, hc12, hc23, hlam, hphi, p2809_1]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        rcases p2809_3 (m.d 0 1) (by simp) with h2828 | h2828
                                        · linarith only [h2496, h2828, hlam]
                                        · linarith only [h0, h2828, hlam]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h2793, hlam, p2809_0]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [hlam, p2809_0]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h0, h2496, h2704, h2796, h2802, hc12, hc23, hlam, hphi, p2809_1]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h0, h2704, h2796, h2802, h2804, hc12, hc23, hlam, hphi, p2809_1]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        rcases p2809_3 (m.d 0 1) (by simp) with h2835 | h2835
                                        · linarith only [h2704, h2835, hlam]
                                        · linarith only [h0, h2835, hlam]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h2794, hlam, p2809_0]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [h2795, hlam, p2809_1]
                                      · have p2809_0 := h2809c.1
                                        have p2809_1 := h2809c.2.1
                                        have p2809_2 := h2809c.2.2.1
                                        have p2809_3 := h2809c.2.2.2
                                        linarith only [hlam, p2809_0]
                                    · rcases h0bigk with h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c | h2841c
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [hlam, p2841_0]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h0, h1, h2796, hc12, hc23, hlam, hphi, p2841_1]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h1, hlam, p2841_0]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h2496, hlam, p2841_1]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h2704, hlam, p2841_1]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h0, hlam, p2841_0]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [hlam, p2841_0]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h2787, hlam, p2841_0]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h2789, hlam, p2841_1]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h2791, hlam, p2841_0]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h0, h1, h2796, hc12, hc23, hlam, hphi, p2841_1]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        rcases p2841_3 (m.d 0 1) (by simp) with h2853 | h2853
                                        · linarith only [h1, h2853, hlam]
                                        · linarith only [h0, h2853, hlam]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [hlam, p2841_0]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h1, h2795, h2796, h2808, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2841_1, u3ehi3]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h0, h1, h2704, h2796, hc12, hc23, hlam, hphi, p2841_1]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h0, h2496, h2796, h2802, hc12, hc23, hlam, hphi, p2841_1]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        rcases p2841_3 (m.d 0 1) (by simp) with h2860 | h2860
                                        · linarith only [h2496, h2860, hlam]
                                        · linarith only [h0, h2860, hlam]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h2793, hlam, p2841_0]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [hlam, p2841_0]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h2496, h2795, h2796, h2802, h2808, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2841_1, u3ehi3]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h0, h2704, h2796, h2802, h2804, hc12, hc23, hlam, hphi, p2841_1]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        rcases p2841_3 (m.d 0 1) (by simp) with h2867 | h2867
                                        · linarith only [h2704, h2867, hlam]
                                        · linarith only [h0, h2867, hlam]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h2794, hlam, p2841_0]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [h2795, hlam, p2841_1]
                                      · have p2841_0 := h2841c.1
                                        have p2841_1 := h2841c.2.1
                                        have p2841_2 := h2841c.2.2.1
                                        have p2841_3 := h2841c.2.2.2
                                        linarith only [hlam, p2841_0]
                                  · linarith only [h0, h2496, h2798, h2807, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1, h2794, h2796, h2806, hlam]
                              · linarith only [h0, h2704, h2796, h2802, h2804, h2805, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1, h2496, h2793, h2795, h2796, h2804, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h2794, h2803, hlam]
                        · linarith only [h1, h2793, h2802, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2879 | h2879
                  · linarith only [h0, h2496, h2879, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2881 | h2881
                    · linarith only [h0, h2496, h2795, h2881, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2883 | h2883
                      · linarith only [h0, h2496, h2795, h2883, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2885 | h2885
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2886 | h2886
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2887 | h2887
                            · linarith only [h0, h2496, h2795, h2879, h2885, h2887, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h2496, h2887, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1, h2794, h2886, hlam]
                        · linarith only [h1, h2794, h2885, hc34, hlam, hphi, u3ehi4]
              · linarith only [h2793, h2794, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2893 | h2893
              · linarith only [h2793, h2893, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2895 | h2895
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2896 | h2896
                  · linarith only [h0, h1, h2896, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2898 | h2898
                    · linarith only [h0, h2789, h2898, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2900 | h2900
                      · linarith only [h0, h1, h2793, h2900, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2902 | h2902
                        · linarith only [h0, h1, h2793, h2896, h2902, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h2902, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2905 | h2905
                  · linarith only [h0, h1, h2905, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2907 | h2907
                    · linarith only [h0, h1, h2793, h2895, h2907, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2909 | h2909
                      · linarith only [h0, h1, h2793, h2895, h2909, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2911 | h2911
                        · linarith only [h0, h1, h2793, h2905, h2911, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h2911, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0 m hb0 hb2 hb3 hb5 hg0 h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x1 m hb0 hb2 hb3 hb5 hg0 h1

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h2915 | h2915
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2916 | h2916
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2917 | h2917
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2918 | h2918
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2919 | h2919
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2920 | h2920
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2921 | h2921
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2922 | h2922
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2923 | h2923
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2924 | h2924
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2925 | h2925
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2926 | h2926
                        · linarith only [h0, h2914, h2926, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h2914, h2920, h2923, h2926, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h2916, h2925, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h2916, h2924, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h2914, h2923, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2932 | h2932
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2933 | h2933
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2934 | h2934
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2935 | h2935
                        · linarith only [h0, h2914, h2935, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h2914, h2920, h2935, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h2916, h2934, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h2916, h2933, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h2914, h2920, h2932, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h2920, h2921, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2942 | h2942
              · linarith only [h2920, h2942, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2944 | h2944
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2945 | h2945
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2946 | h2946
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2947 | h2947
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2948 | h2948
                        · linarith only [h2914, h2920, h2948, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2950 | h2950
                          · linarith only [h2914, h2942, h2950, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2952 | h2952
                            · linarith only [h0, h2915, h2952, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h0, h2915, h2944, h2945, h2948, h2952, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h2915, h2944, h2947, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h2914, h2945, h2946, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2914, h2945, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2958 | h2958
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2959 | h2959
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2960 | h2960
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2961 | h2961
                        · linarith only [h0, h2914, h2920, h2961, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2963 | h2963
                          · linarith only [h2914, h2942, h2963, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2965 | h2965
                            · linarith only [h2915, h2944, h2965, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2967 | h2967
                              · linarith only [h2914, h2920, h2958, h2967, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2969 | h2969
                                · linarith only [h2914, h2942, h2958, h2969, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2971 | h2971
                                  · linarith only [h2915, h2944, h2959, h2971, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2973 | h2973
                                    · linarith only [h2914, h2920, h2944, h2958, h2973, hc34, hlam, hphi, u3ehi2]
                                    · linarith only [h2914, h2920, h2958, h2973, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h2916, h2960, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h2914, h2958, h2959, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2914, h2958, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h2916, h2919, hlam]
        · linarith only [h0, h2915, h2918, hlam]
      · linarith only [h0, h2914, h2917, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2982 | h2982
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2983 | h2983
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2984 | h2984
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2985 | h2985
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2986 | h2986
              · linarith only [h2914, h2916, h2986, hlam]
              · linarith only [h2985, h2986, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2989 | h2989
              · linarith only [h2985, h2989, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2991 | h2991
                · linarith only [h2915, h2916, h2991, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2993 | h2993
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2994 | h2994
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2995 | h2995
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2996 | h2996
                        · linarith only [h2914, h2985, h2996, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2998 | h2998
                          · linarith only [h2914, h2985, h2998, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h2915, h2916, h2996, h2998, hc35, hlam, hphi, u3ehi1]
                      · linarith only [h0, h2984, h2995, hlam]
                    · linarith only [h0, h2914, h2993, h2994, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2914, h2993, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3004 | h3004
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3005 | h3005
              · linarith only [h2914, h2916, h3005, hlam]
              · linarith only [h3004, h3005, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3008 | h3008
              · linarith only [h3004, h3008, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3010 | h3010
                · linarith only [h0, h2915, h2984, h3010, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3012 | h3012
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3013 | h3013
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3014 | h3014
                      · linarith only [h0, h2914, h2984, h3012, h3014, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h2914, h3012, h3014, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h2914, h3012, h3013, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2914, h3012, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h0, h2915, h2983, hlam]
      · linarith only [h0, h2914, h2982, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3021 | h3021
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3022 | h3022
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3023 | h3023
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3024 | h3024
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3025 | h3025
            · linarith only [h2914, h2915, h3025, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3027 | h3027
              · linarith only [h3025, h3027, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3029 | h3029
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3030 | h3030
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3031 | h3031
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3032 | h3032
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3033 | h3033
                        · linarith only [h2914, h2915, h3025, h3031, h3033, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h2914, h2915, h3030, h3033, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h2914, h2915, h3030, h3031, h3032, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h3023, h3031, hlam]
                  · linarith only [h0, h2914, h3030, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h2914, h2915, h3029, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h3021, h3024, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3041 | h3041
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3042 | h3042
            · linarith only [h0, h2914, h3023, h3042, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3044 | h3044
              · linarith only [h3042, h3044, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3046 | h3046
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3047 | h3047
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3048 | h3048
                    · linarith only [h0, h3021, h3023, h3048, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                    · linarith only [h0, h2914, h3047, h3048, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2914, h3047, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h2914, h2915, h3046, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h3021, h3041, hlam]
      · linarith only [h0, h2914, h3022, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3055 | h3055
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3056 | h3056
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3057 | h3057
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3058 | h3058
            · linarith only [h2914, h2915, h3058, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3060 | h3060
              · linarith only [h3058, h3060, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3062 | h3062
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3063 | h3063
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3064 | h3064
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3065 | h3065
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3066 | h3066
                        · linarith only [h2914, h3058, h3066, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h2914, h2915, h3063, h3066, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h0, h3057, h3065, hlam]
                    · linarith only [h0, h3056, h3064, hlam]
                  · linarith only [h0, h2914, h3063, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h2914, h2915, h3062, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3073 | h3073
            · linarith only [h2914, h2915, h3073, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3075 | h3075
              · linarith only [h3073, h3075, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3077 | h3077
                · linarith only [h3056, h3057, h3077, hlam]
                · linarith only [h2914, h2915, h3077, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3080 | h3080
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3081 | h3081
            · linarith only [h2914, h3021, h3056, h3080, h3081, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3083 | h3083
              · linarith only [h3081, h3083, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3085 | h3085
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3086 | h3086
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3087 | h3087
                    · linarith only [h2914, h3021, h3056, h3080, h3087, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h2914, h3086, h3087, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2914, h3086, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h2914, h3021, h3056, h3080, h3085, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3092 | h3092
            · linarith only [h0, h2914, h3056, h3092, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3094 | h3094
              · linarith only [h3092, h3094, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3096 | h3096
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3097 | h3097
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3098 | h3098
                    · linarith only [h0, h2914, h3056, h3097, h3098, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h2914, h3097, h3098, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2914, h3097, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h2914, h2915, h3096, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h0, h2914, h3055, hlam]

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h3105 | h3105
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3106 | h3106
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3107 | h3107
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3108 | h3108
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3109 | h3109
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3110 | h3110
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3111 | h3111
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3112 | h3112
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3113 | h3113
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3114 | h3114
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3115 | h3115
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3116 | h3116
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3117 | h3117
                          · linarith only [h2914, h3104, h3112, h3117, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h2914, h3104, h3111, h3112, h3115, h3117, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h2914, h3105, h3116, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h2914, h3105, h3115, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h2914, h3104, h3111, h3112, h3114, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h2914, h3104, h3111, h3112, h3113, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h3104, h3106, h3111, h3112, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3125 | h3125
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3126 | h3126
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3127 | h3127
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3128 | h3128
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3129 | h3129
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3130 | h3130
                          · linarith only [h3104, h3111, h3130, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3132 | h3132
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3133 | h3133
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3134 | h3134
                                · linarith only [h3104, h3111, h3126, h3134, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3136 | h3136
                                  · linarith only [h3104, h3111, h3126, h3132, h3136, hlam]
                                  · rcases h0bigk with h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c | h3138c
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h0, hlam, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2914, hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2914, h3104, h3126, h3132, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3138_1, u3ehi3]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h2914, hc13, hlam, hphi, ht01, ht0b, ht5b, p3138_1, u5ehi0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h0, h3104, h3126, h3132, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3138_1, u3ehi3]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h0, h2914, h3105, h3126, h3130, h3132, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3138_1, u3ehi3]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      rcases p3138_3 (m.d 0 1) (by simp) with h3147 | h3147
                                      · linarith only [h0, h3147, hlam]
                                      · linarith only [h3104, h3147, hlam]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      rcases p3138_3 (m.d 0 1) (by simp) with h3150 | h3150
                                      · linarith only [h0, h3150, hlam]
                                      · linarith only [h3105, h3150, hlam]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h3105, h3126, h3130, h3132, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p3138_1, u3ehi3]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h3106, hlam, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      rcases p3138_3 (m.d 0 1) (by simp) with h3156 | h3156
                                      · linarith only [h2914, h3156, hlam]
                                      · linarith only [h3104, h3156, hlam]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      rcases p3138_3 (m.d 0 1) (by simp) with h3159 | h3159
                                      · linarith only [h2914, h3159, hlam]
                                      · linarith only [h3105, h3159, hlam]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h3104, hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h3107, hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h3109, hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h3111, hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h3105, hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h3108, hlam, p3138_1]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h3110, hlam, p3138_0]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [h0, h3104, h3105, h3126, h3132, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3138_1, u3ehi3]
                                    · have p3138_0 := h3138c.1
                                      have p3138_1 := h3138c.2.1
                                      have p3138_2 := h3138c.2.2.1
                                      have p3138_3 := h3138c.2.2.2
                                      linarith only [hlam, p3138_0]
                              · linarith only [h2914, h3105, h3125, h3129, h3133, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h3109, h3111, h3132, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h2914, h3105, h3129, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h2914, h3105, h3127, h3128, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h3105, h3127, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h2914, h3105, h3125, h3126, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h3105, h3125, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h3109, h3110, hc35, hlam, hphi, u3ehi3]
          · linarith only [h2914, h3104, h3109, hlam]
        · linarith only [h0, h3105, h3108, hlam]
      · linarith only [h2914, h3104, h3106, h3107, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3183 | h3183
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3184 | h3184
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3185 | h3185
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3186 | h3186
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3187 | h3187
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3188 | h3188
                · linarith only [h3106, h3184, h3188, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h3104, h3187, h3188, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3191 | h3191
                · linarith only [h0, h3105, h3106, h3191, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h3105, h3191, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h3185, h3186, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h3104, h3106, h3185, hlam]
        · linarith only [h0, h3105, h3184, hlam]
      · linarith only [h0, h3104, h3183, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3198 | h3198
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3199 | h3199
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3200 | h3200
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3201 | h3201
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3202 | h3202
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3203 | h3203
              · linarith only [h3104, h3105, h3203, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3205 | h3205
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3206 | h3206
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3207 | h3207
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3208 | h3208
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3209 | h3209
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3210 | h3210
                          · linarith only [h3104, h3105, h3203, h3205, h3209, h3210, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h3104, h3105, h3208, h3210, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h0, h2914, h3104, h3198, h3202, h3208, h3209, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h2914, h3201, h3208, hlam]
                    · linarith only [h0, h3198, h3200, h3202, h3207, hlam]
                  · linarith only [h0, h3199, h3206, hlam]
                · linarith only [h0, h3198, h3205, hlam]
            · linarith only [h3201, h3202, hc35, hlam, hphi, u3ehi3]
          · linarith only [h2914, h3104, h3201, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3220 | h3220
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3221 | h3221
            · linarith only [h3198, h3200, h3221, hlam]
            · linarith only [h3220, h3221, hc35, hlam, hphi, u3ehi3]
          · linarith only [h2914, h3104, h3220, hlam]
      · linarith only [h0, h3104, h3199, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3226 | h3226
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3227 | h3227
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3228 | h3228
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3229 | h3229
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3230 | h3230
              · linarith only [h3104, h3105, h3230, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3232 | h3232
                · linarith only [h3198, h3227, h3232, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3234 | h3234
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3235 | h3235
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3236 | h3236
                      · linarith only [h0, h3104, h3232, h3236, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h2914, h3229, h3236, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h0, h3104, h3227, h3228, h3235, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h3226, h3234, hlam]
            · linarith only [h3228, h3229, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h3104, h3198, h3228, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3243 | h3243
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3244 | h3244
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3245 | h3245
              · linarith only [h0, h3104, h3227, h3245, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3247 | h3247
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3248 | h3248
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3249 | h3249
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3250 | h3250
                      · linarith only [h0, h3104, h3198, h3247, h3250, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h3104, h3198, h3243, h3247, h3250, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h3104, h3198, h3243, h3247, h3249, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h3104, h3198, h3243, h3247, h3248, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3255 | h3255
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3256 | h3256
                    · linarith only [h0, h3104, h3227, h3243, h3247, h3256, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3258 | h3258
                      · linarith only [h0, h3104, h3247, h3258, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h2914, h3243, h3245, h3258, hc45, hlam, hphi, ht34, u3ehi0]
                  · linarith only [h0, h3104, h3226, h3227, h3255, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h3243, h3244, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h3104, h3198, h3243, hlam]
      · linarith only [h0, h3104, h3226, hlam]

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h3266 | h3266
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3267 | h3267
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3268 | h3268
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3269 | h3269
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3270 | h3270
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3271 | h3271
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3272 | h3272
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3273 | h3273
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3274 | h3274
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3275 | h3275
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3276 | h3276
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3277 | h3277
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3278 | h3278
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3279 | h3279
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3280 | h3280
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3281 | h3281
                                · linarith only [h3266, h3278, h3281, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h3104, h3265, h3272, h3275, h3277, h3281, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h3104, h3265, h3272, h3275, h3277, h3278, h3280, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h3104, h3265, h3272, h3275, h3276, h3279, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3286 | h3286
                            · linarith only [h3278, h3286, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h3104, h3265, h3272, h3275, h3276, h3286, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h3104, h3265, h3277, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                      · linarith only [h3104, h3265, h3275, h3276, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h2914, h3265, h3269, h3274, h3275, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · linarith only [h2914, h3265, h3272, h3274, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h2914, h3265, h3272, h3273, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h3266, h3272, hlam]
            · linarith only [h3104, h3265, h3271, hlam]
          · linarith only [h3269, h3270, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3297 | h3297
          · linarith only [h3269, h3297, hc34, hlam, hphi, u3ehi4]
          · linarith only [h2914, h3265, h3297, hlam]
      · linarith only [h0, h3265, h3268, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3301 | h3301
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3302 | h3302
        · linarith only [h3266, h3267, h3302, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3304 | h3304
          · linarith only [h3302, h3304, hc34, hlam, hphi, u3ehi4]
          · linarith only [h2914, h3265, h3304, hlam]
      · linarith only [h2914, h3265, h3266, h3301, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3308 | h3308
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3309 | h3309
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3310 | h3310
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3311 | h3311
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3312 | h3312
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3313 | h3313
              · linarith only [h3266, h3309, h3313, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h3265, h3313, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h3104, h3265, h3312, hlam]
          · linarith only [h3310, h3311, hc35, hlam, hphi, u3ehi3]
        · linarith only [h3266, h3308, h3310, hlam]
      · linarith only [h3104, h3265, h3308, h3309, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3320 | h3320
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3321 | h3321
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3322 | h3322
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3323 | h3323
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3324 | h3324
              · linarith only [h3266, h3320, h3324, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h3265, h3324, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h3265, h3308, h3323, hlam]
          · linarith only [h3321, h3322, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3329 | h3329
          · linarith only [h3321, h3329, hc34, hlam, hphi, u3ehi4]
          · linarith only [h2914, h3265, h3329, hlam]
      · linarith only [h0, h3265, h3320, hlam]

end R2N4
