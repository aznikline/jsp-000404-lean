import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_48S6
import Jsp000404.R1LeavesN7_48S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1464 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1586 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1647 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 5 (by decide) (by decide) with h2426 | h2426
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2427 | h2427
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2428 | h2428
      · linarith only [h0, h1647, h2, h2426, h2428, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2430 | h2430
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2431 | h2431
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2432 | h2432
            · rcases h2bigk with h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h1586, h2, h2428, h2430, h5, hlam, p2433_2]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                rcases p2433_3 (m.d 0 2) (by simp) with h2436 | h2436
                · rcases p2433_3 (m.d 1 2) (by simp) with h2437 | h2437
                  · linarith only [h0, h2437, hlam]
                  · rcases p2433_3 (m.d 2 3) (by simp) with h2439 | h2439
                    · linarith only [h2439, hlam, p2433_0]
                    · rcases p2433_3 (m.d 2 4) (by simp) with h2441 | h2441
                      · linarith only [h2441, h3, hlam]
                      · linarith only [h2428, h2441, hlam]
                · linarith only [h2436, hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                rcases p2433_3 (m.d 0 2) (by simp) with h2445 | h2445
                · rcases p2433_3 (m.d 1 2) (by simp) with h2446 | h2446
                  · linarith only [h0, h2446, hlam]
                  · rcases p2433_3 (m.d 2 3) (by simp) with h2448 | h2448
                    · linarith only [h2, h2448, hlam]
                    · rcases p2433_3 (m.d 2 4) (by simp) with h2450 | h2450
                      · linarith only [h2450, hlam, p2433_0]
                      · rcases p2433_3 (m.d 2 5) (by simp) with h2452 | h2452
                        · linarith only [h2452, h4, hlam]
                        · rcases h3bigk with h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c | h2454c
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            rcases p2454_3 (m.d 0 3) (by simp) with h2456 | h2456
                            · rcases p2454_3 (m.d 1 3) (by simp) with h2457 | h2457
                              · linarith only [h1, h2457, hlam]
                              · rcases p2454_3 (m.d 2 3) (by simp) with h2459 | h2459
                                · linarith only [h2, h2459, hlam]
                                · linarith only [h2459, h8, hlam]
                            · linarith only [h1, h2456, hlam]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            rcases p2454_3 (m.d 0 3) (by simp) with h2463 | h2463
                            · rcases p2454_3 (m.d 1 3) (by simp) with h2464 | h2464
                              · linarith only [h1, h2464, hlam]
                              · rcases p2454_3 (m.d 2 3) (by simp) with h2466 | h2466
                                · linarith only [h2, h2466, hlam]
                                · rcases p2454_3 (m.d 3 4) (by simp) with h2468 | h2468
                                  · linarith only [h2468, h5, hlam]
                                  · linarith only [h2428, h2468, hlam]
                            · linarith only [h2, h2463, hlam]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h1586, h2, h2428, h2430, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2454_1]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h2426, h2428, h5, h8, hlam, p2454_2]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h1, hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h8, hlam, p2454_1]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h1647, hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h2428, h5, h8, hc03, hc35, hlam, hphi, ht0b, ht5b, p2454_1]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h2, hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h2428, h5, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2454_1]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h2428, hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h0, h2, h2428, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p2454_1]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h5, hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h0, h2, h2426, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p2454_1]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h0, h2, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2454_1]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            rcases p2454_3 (m.d 0 3) (by simp) with h2488 | h2488
                            · rcases p2454_3 (m.d 1 3) (by simp) with h2489 | h2489
                              · linarith only [h1647, h2489, hlam]
                              · linarith only [h2426, h2489, hlam]
                            · linarith only [h2488, h6, hlam]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h6, hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h2426, hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h2430, hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [h2432, hlam, p2454_0]
                          · have p2454_0 := h2454c.1
                            have p2454_1 := h2454c.2.1
                            have p2454_2 := h2454c.2.2.1
                            have p2454_3 := h2454c.2.2.2
                            linarith only [hlam, p2454_0]
                · linarith only [h2445, hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                rcases p2433_3 (m.d 0 2) (by simp) with h2499 | h2499
                · rcases p2433_3 (m.d 1 2) (by simp) with h2500 | h2500
                  · linarith only [h0, h2500, hlam]
                  · rcases p2433_3 (m.d 2 3) (by simp) with h2502 | h2502
                    · linarith only [h2, h2502, hlam]
                    · linarith only [h2430, h2502, hlam]
                · linarith only [h2499, hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h0, hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h8, hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h1464, hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h1586, hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h2, hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h0, h2, h2428, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2433_1]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h2428, hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h0, h1586, h2, h2428, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2433_1]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h3, hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                rcases p2433_3 (m.d 0 2) (by simp) with h2517 | h2517
                · rcases p2433_3 (m.d 1 2) (by simp) with h2518 | h2518
                  · linarith only [h2518, hlam, p2433_0]
                  · rcases p2433_3 (m.d 2 3) (by simp) with h2520 | h2520
                    · linarith only [h2428, h2520, hlam]
                    · linarith only [h2520, h8, hlam]
                · linarith only [h0, h2517, hlam]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h0, h3, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2433_1]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h0, h1586, h2, h2428, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2433_1]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h4, hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h0, h2, h2428, h2430, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2433_1]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h2430, hlam, p2433_1]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [h2431, hlam, p2433_0]
              · have p2433_0 := h2433c.1
                have p2433_1 := h2433c.2.1
                have p2433_2 := h2433c.2.2.1
                have p2433_3 := h2433c.2.2.2
                linarith only [hlam, p2433_0]
            · linarith only [h0, h2, h2428, h2432, h5, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h0, h1464, h1586, h2, h2427, h2428, h2430, h2431, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h2426, h2430, h8, hlam]
    · linarith only [h1647, h2426, h2427, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2536 | h2536
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2537 | h2537
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2538 | h2538
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2539 | h2539
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2540 | h2540
            · rcases h2bigk with h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c | h2541c
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h2, h2426, h2537, h2540, h8, hlam, p2541_2]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h2426, h2537, h2540, h8, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2541_1]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                rcases p2541_3 (m.d 0 2) (by simp) with h2545 | h2545
                · rcases p2541_3 (m.d 1 2) (by simp) with h2546 | h2546
                  · linarith only [h0, h2546, hlam]
                  · rcases p2541_3 (m.d 2 3) (by simp) with h2548 | h2548
                    · linarith only [h2, h2548, hlam]
                    · linarith only [h2537, h2548, hlam]
                · linarith only [h2545, hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                rcases p2541_3 (m.d 0 2) (by simp) with h2552 | h2552
                · rcases p2541_3 (m.d 1 2) (by simp) with h2553 | h2553
                  · linarith only [h0, h2553, hlam]
                  · rcases p2541_3 (m.d 2 3) (by simp) with h2555 | h2555
                    · linarith only [h2, h2555, hlam]
                    · linarith only [h2538, h2555, hlam]
                · linarith only [h2552, hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h0, hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h8, hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h1464, hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h1586, hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h2, hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                rcases p2541_3 (m.d 0 2) (by simp) with h2565 | h2565
                · rcases p2541_3 (m.d 1 2) (by simp) with h2566 | h2566
                  · linarith only [h2566, hlam, p2541_0]
                  · rcases p2541_3 (m.d 2 3) (by simp) with h2568 | h2568
                    · rcases p2541_3 (m.d 2 4) (by simp) with h2569 | h2569
                      · linarith only [h2537, h2569, hlam]
                      · linarith only [h1464, h2569, hlam]
                    · linarith only [h2568, hlam, p2541_0]
                · linarith only [h0, h2565, hlam]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h2426, h2538, h2539, h8, hc12, hc23, hlam, hphi, p2541_1]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h0, h2, h2426, h2538, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2541_1]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h3, hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                rcases p2541_3 (m.d 0 2) (by simp) with h2578 | h2578
                · rcases p2541_3 (m.d 1 2) (by simp) with h2579 | h2579
                  · linarith only [h2579, hlam, p2541_0]
                  · rcases p2541_3 (m.d 2 3) (by simp) with h2581 | h2581
                    · rcases p2541_3 (m.d 2 4) (by simp) with h2582 | h2582
                      · rcases p2541_3 (m.d 2 5) (by simp) with h2583 | h2583
                        · linarith only [h2539, h2583, hlam]
                        · linarith only [h1586, h2583, hlam]
                      · linarith only [h2582, hlam, p2541_0]
                    · linarith only [h2581, h8, hlam]
                · linarith only [h0, h2578, hlam]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h2537, hlam, p2541_1]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h2426, h2538, h8, hc12, hc24, hlam, hphi, p2541_1]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h4, hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                rcases p2541_3 (m.d 0 2) (by simp) with h2593 | h2593
                · rcases p2541_3 (m.d 1 2) (by simp) with h2594 | h2594
                  · linarith only [h2594, hlam, p2541_0]
                  · rcases p2541_3 (m.d 2 3) (by simp) with h2596 | h2596
                    · rcases p2541_3 (m.d 2 4) (by simp) with h2597 | h2597
                      · rcases p2541_3 (m.d 2 5) (by simp) with h2598 | h2598
                        · rcases h3bigk with h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c | h2599c
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            rcases p2599_3 (m.d 0 3) (by simp) with h2601 | h2601
                            · rcases p2599_3 (m.d 1 3) (by simp) with h2602 | h2602
                              · linarith only [h1, h2602, hlam]
                              · rcases p2599_3 (m.d 2 3) (by simp) with h2604 | h2604
                                · linarith only [h2, h2604, hlam]
                                · linarith only [h2604, h8, hlam]
                            · linarith only [h1, h2601, hlam]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h0, h2, h2426, h2537, h2540, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2599_1]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            rcases p2599_3 (m.d 0 3) (by simp) with h2609 | h2609
                            · rcases p2599_3 (m.d 1 3) (by simp) with h2610 | h2610
                              · linarith only [h1, h2610, hlam]
                              · rcases p2599_3 (m.d 2 3) (by simp) with h2612 | h2612
                                · linarith only [h2, h2612, hlam]
                                · linarith only [h2537, h2612, hlam]
                            · linarith only [h2609, hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            rcases p2599_3 (m.d 0 3) (by simp) with h2616 | h2616
                            · rcases p2599_3 (m.d 1 3) (by simp) with h2617 | h2617
                              · linarith only [h1, h2617, hlam]
                              · rcases p2599_3 (m.d 2 3) (by simp) with h2619 | h2619
                                · linarith only [h2, h2619, hlam]
                                · linarith only [h2538, h2619, hlam]
                            · linarith only [h2616, hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h1, hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h8, hlam, p2599_1]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h1647, hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h2426, hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h2, hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            rcases p2599_3 (m.d 0 3) (by simp) with h2629 | h2629
                            · rcases p2599_3 (m.d 1 3) (by simp) with h2630 | h2630
                              · linarith only [h2630, h8, hlam]
                              · rcases p2599_3 (m.d 2 3) (by simp) with h2632 | h2632
                                · rcases p2599_3 (m.d 3 4) (by simp) with h2633 | h2633
                                  · linarith only [h2537, h2633, hlam]
                                  · linarith only [h1647, h2633, hlam]
                                · linarith only [h2632, h8, hlam]
                            · linarith only [h1, h2629, hlam]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h2426, h2540, h8, hc12, hc23, hlam, hphi, p2599_1]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h0, h2, h2426, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2599_1]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h5, hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h0, h2, h2537, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2599_1]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h2537, hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h0, h2, h2426, h2537, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2599_1]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h6, hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h0, h2, h2538, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2599_1]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h2538, hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [h2540, hlam, p2599_0]
                          · have p2599_0 := h2599c.1
                            have p2599_1 := h2599c.2.1
                            have p2599_2 := h2599c.2.2.1
                            have p2599_3 := h2599c.2.2.2
                            linarith only [hlam, p2599_0]
                        · linarith only [h2598, hlam, p2541_0]
                      · linarith only [h1464, h2597, hlam]
                    · linarith only [h2596, h8, hlam]
                · linarith only [h0, h2593, hlam]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h2538, hlam, p2541_1]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [h2539, hlam, p2541_0]
              · have p2541_0 := h2541c.1
                have p2541_1 := h2541c.2.1
                have p2541_2 := h2541c.2.2.1
                have p2541_3 := h2541c.2.2.2
                linarith only [hlam, p2541_0]
            · linarith only [h0, h1464, h1647, h2, h2536, h2537, h2540, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h0, h1464, h2, h2426, h2536, h2538, h2539, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h0, h1647, h2, h2536, h2537, h2538, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2661 | h2661
        · linarith only [h2426, h2537, h2661, h8, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2663 | h2663
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2664 | h2664
            · rcases h2bigk with h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c | h2665c
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h2, h2661, h2664, h5, h8, hlam, p2665_2]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                rcases p2665_3 (m.d 0 2) (by simp) with h2668 | h2668
                · rcases p2665_3 (m.d 1 2) (by simp) with h2669 | h2669
                  · linarith only [h0, h2669, hlam]
                  · rcases p2665_3 (m.d 2 3) (by simp) with h2671 | h2671
                    · linarith only [h2671, hlam, p2665_0]
                    · rcases p2665_3 (m.d 2 4) (by simp) with h2673 | h2673
                      · linarith only [h2673, h3, hlam]
                      · linarith only [h2537, h2673, hlam]
                · linarith only [h2668, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                rcases p2665_3 (m.d 0 2) (by simp) with h2677 | h2677
                · rcases p2665_3 (m.d 1 2) (by simp) with h2678 | h2678
                  · linarith only [h0, h2678, hlam]
                  · rcases p2665_3 (m.d 2 3) (by simp) with h2680 | h2680
                    · linarith only [h2, h2680, hlam]
                    · rcases p2665_3 (m.d 2 4) (by simp) with h2682 | h2682
                      · linarith only [h2682, hlam, p2665_0]
                      · rcases p2665_3 (m.d 2 5) (by simp) with h2684 | h2684
                        · linarith only [h2684, h4, hlam]
                        · rcases h3bigk with h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c | h2686c
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            rcases p2686_3 (m.d 0 3) (by simp) with h2688 | h2688
                            · rcases p2686_3 (m.d 1 3) (by simp) with h2689 | h2689
                              · linarith only [h1, h2689, hlam]
                              · rcases p2686_3 (m.d 2 3) (by simp) with h2691 | h2691
                                · linarith only [h2, h2691, hlam]
                                · linarith only [h2691, h8, hlam]
                            · linarith only [h1, h2688, hlam]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            rcases p2686_3 (m.d 0 3) (by simp) with h2695 | h2695
                            · rcases p2686_3 (m.d 1 3) (by simp) with h2696 | h2696
                              · linarith only [h1, h2696, hlam]
                              · rcases p2686_3 (m.d 2 3) (by simp) with h2698 | h2698
                                · linarith only [h2, h2698, hlam]
                                · rcases p2686_3 (m.d 3 4) (by simp) with h2700 | h2700
                                  · linarith only [h2700, h5, hlam]
                                  · linarith only [h2537, h2700, hlam]
                            · linarith only [h2, h2695, hlam]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h0, h2, h2661, h2664, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2686_1]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h0, h2, h2661, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2686_1]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h1, hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h8, hlam, p2686_1]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h1647, hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h2426, hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h2, hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h2661, h2664, hc13, hc34, hlam, hphi, p2686_1]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h2537, hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h2661, hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h5, hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            rcases p2686_3 (m.d 0 3) (by simp) with h2717 | h2717
                            · rcases p2686_3 (m.d 1 3) (by simp) with h2718 | h2718
                              · linarith only [h2718, hlam, p2686_0]
                              · rcases p2686_3 (m.d 2 3) (by simp) with h2720 | h2720
                                · linarith only [h2537, h2720, hlam]
                                · linarith only [h2720, h8, hlam]
                            · linarith only [h1, h2717, hlam]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h0, h2, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2686_1]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h0, h2, h2426, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2686_1]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h6, hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            rcases p2686_3 (m.d 0 3) (by simp) with h2728 | h2728
                            · rcases p2686_3 (m.d 1 3) (by simp) with h2729 | h2729
                              · linarith only [h2729, hlam, p2686_0]
                              · rcases p2686_3 (m.d 2 3) (by simp) with h2731 | h2731
                                · linarith only [h2661, h2731, hlam]
                                · linarith only [h2731, h8, hlam]
                            · linarith only [h1, h2728, hlam]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h8, hc12, hc35, hlam, hphi, ht23, p2686_1]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [h2664, hlam, p2686_0]
                          · have p2686_0 := h2686c.1
                            have p2686_1 := h2686c.2.1
                            have p2686_2 := h2686c.2.2.1
                            have p2686_3 := h2686c.2.2.2
                            linarith only [hlam, p2686_0]
                · linarith only [h2677, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                rcases p2665_3 (m.d 0 2) (by simp) with h2739 | h2739
                · rcases p2665_3 (m.d 1 2) (by simp) with h2740 | h2740
                  · linarith only [h0, h2740, hlam]
                  · rcases p2665_3 (m.d 2 3) (by simp) with h2742 | h2742
                    · linarith only [h2, h2742, hlam]
                    · rcases p2665_3 (m.d 2 4) (by simp) with h2744 | h2744
                      · linarith only [h2744, h3, hlam]
                      · linarith only [h2663, h2744, hlam]
                · linarith only [h2739, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h0, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h8, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h1464, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h1586, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h2, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h0, h2, h2537, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2665_1]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h2537, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h2661, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h3, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                rcases p2665_3 (m.d 0 2) (by simp) with h2759 | h2759
                · rcases p2665_3 (m.d 1 2) (by simp) with h2760 | h2760
                  · linarith only [h2760, hlam, p2665_0]
                  · rcases p2665_3 (m.d 2 3) (by simp) with h2762 | h2762
                    · linarith only [h2537, h2762, hlam]
                    · linarith only [h2762, h8, hlam]
                · linarith only [h0, h2759, hlam]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h8, hc12, hc24, hlam, hphi, p2665_1]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h0, h1586, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2665_1]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h4, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                rcases p2665_3 (m.d 0 2) (by simp) with h2770 | h2770
                · rcases p2665_3 (m.d 1 2) (by simp) with h2771 | h2771
                  · linarith only [h2771, hlam, p2665_0]
                  · rcases p2665_3 (m.d 2 3) (by simp) with h2773 | h2773
                    · linarith only [h2661, h2773, hlam]
                    · linarith only [h2773, h8, hlam]
                · linarith only [h0, h2770, hlam]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h8, hc12, hc25, hlam, hphi, p2665_1]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [h2663, hlam, p2665_0]
              · have p2665_0 := h2665c.1
                have p2665_1 := h2665c.2.1
                have p2665_2 := h2665c.2.2.1
                have p2665_3 := h2665c.2.2.2
                linarith only [hlam, p2665_0]
            · linarith only [h1464, h2536, h2537, h2664, hlam]
          · linarith only [h1464, h2536, h2663, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2782 | h2782
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2783 | h2783
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2784 | h2784
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2785 | h2785
            · linarith only [h0, h2, h2536, h2782, h2785, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1647, h2, h2782, h2784, h2785, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2788 | h2788
            · linarith only [h0, h1464, h2, h2784, h2788, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h2bigk with h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c | h2790c
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h1647, h2, h2782, h8, hlam, p2790_2]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h0, h1647, h2782, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2790_1]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                rcases p2790_3 (m.d 0 2) (by simp) with h2794 | h2794
                · rcases p2790_3 (m.d 1 2) (by simp) with h2795 | h2795
                  · linarith only [h0, h2795, hlam]
                  · rcases p2790_3 (m.d 2 3) (by simp) with h2797 | h2797
                    · linarith only [h2, h2797, hlam]
                    · linarith only [h2782, h2797, hlam]
                · linarith only [h2794, hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                rcases p2790_3 (m.d 0 2) (by simp) with h2801 | h2801
                · rcases p2790_3 (m.d 1 2) (by simp) with h2802 | h2802
                  · linarith only [h0, h2802, hlam]
                  · rcases p2790_3 (m.d 2 3) (by simp) with h2804 | h2804
                    · linarith only [h2, h2804, hlam]
                    · linarith only [h2783, h2804, hlam]
                · linarith only [h2801, hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h0, hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h8, hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h1464, hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h1586, hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h2, hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                rcases p2790_3 (m.d 0 2) (by simp) with h2814 | h2814
                · rcases p2790_3 (m.d 1 2) (by simp) with h2815 | h2815
                  · linarith only [h2815, hlam, p2790_0]
                  · rcases p2790_3 (m.d 2 3) (by simp) with h2817 | h2817
                    · rcases p2790_3 (m.d 2 4) (by simp) with h2818 | h2818
                      · linarith only [h2782, h2818, hlam]
                      · linarith only [h1464, h2818, hlam]
                    · linarith only [h2817, hlam, p2790_0]
                · linarith only [h0, h2814, hlam]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h1647, h2782, h8, hc12, hc23, hlam, hphi, p2790_1]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h0, h1586, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2790_1]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h3, hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h2784, hc12, hc45, hlam, hphi, ht23, ht34, p2790_1]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h2782, hlam, p2790_1]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h2784, hlam, p2790_1]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h4, hlam, p2790_0]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                rcases p2790_3 (m.d 0 2) (by simp) with h2832 | h2832
                · rcases p2790_3 (m.d 1 2) (by simp) with h2833 | h2833
                  · linarith only [h2833, hlam, p2790_0]
                  · rcases p2790_3 (m.d 2 3) (by simp) with h2835 | h2835
                    · rcases p2790_3 (m.d 2 4) (by simp) with h2836 | h2836
                      · linarith only [h2784, h2836, hlam]
                      · linarith only [h1464, h2836, hlam]
                    · linarith only [h2835, h8, hlam]
                · linarith only [h0, h2832, hlam]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h2783, hlam, p2790_1]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [h0, h1464, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2790_1]
              · have p2790_0 := h2790c.1
                have p2790_1 := h2790c.2.1
                have p2790_2 := h2790c.2.2.1
                have p2790_3 := h2790c.2.2.2
                linarith only [hlam, p2790_0]
        · linarith only [h0, h1647, h2, h2782, h2783, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2845 | h2845
        · linarith only [h2426, h2782, h2845, h8, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2847 | h2847
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2848 | h2848
            · rcases h2bigk with h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c | h2849c
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h1647, h2536, h2847, h3, h8, hlam, p2849_2]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                rcases p2849_3 (m.d 0 2) (by simp) with h2852 | h2852
                · rcases p2849_3 (m.d 1 2) (by simp) with h2853 | h2853
                  · linarith only [h0, h2853, hlam]
                  · rcases p2849_3 (m.d 2 3) (by simp) with h2855 | h2855
                    · linarith only [h2855, hlam, p2849_0]
                    · rcases p2849_3 (m.d 2 4) (by simp) with h2857 | h2857
                      · linarith only [h2857, h3, hlam]
                      · linarith only [h2782, h2857, hlam]
                · linarith only [h2852, hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h0, h1647, h2536, h2847, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2849_1]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                rcases p2849_3 (m.d 0 2) (by simp) with h2862 | h2862
                · rcases p2849_3 (m.d 1 2) (by simp) with h2863 | h2863
                  · linarith only [h0, h2863, hlam]
                  · rcases p2849_3 (m.d 2 3) (by simp) with h2865 | h2865
                    · linarith only [h2, h2865, hlam]
                    · rcases p2849_3 (m.d 2 4) (by simp) with h2867 | h2867
                      · linarith only [h2867, h3, hlam]
                      · linarith only [h2847, h2867, hlam]
                · linarith only [h2862, hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h0, hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h8, hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h1464, hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h1586, hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h2, hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h0, h2, h2845, h2848, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2849_1]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h2782, hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h2845, hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h3, hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                rcases p2849_3 (m.d 0 2) (by simp) with h2882 | h2882
                · rcases p2849_3 (m.d 1 2) (by simp) with h2883 | h2883
                  · linarith only [h2883, hlam, p2849_0]
                  · rcases p2849_3 (m.d 2 3) (by simp) with h2885 | h2885
                    · linarith only [h2782, h2885, hlam]
                    · linarith only [h2885, h8, hlam]
                · linarith only [h0, h2882, hlam]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h8, hc12, hc24, hlam, hphi, p2849_1]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h0, h1586, h2, h2782, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2849_1]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h4, hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                rcases p2849_3 (m.d 0 2) (by simp) with h2893 | h2893
                · rcases p2849_3 (m.d 1 2) (by simp) with h2894 | h2894
                  · linarith only [h2894, hlam, p2849_0]
                  · rcases p2849_3 (m.d 2 3) (by simp) with h2896 | h2896
                    · linarith only [h2845, h2896, hlam]
                    · linarith only [h2896, h8, hlam]
                · linarith only [h0, h2893, hlam]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h8, hc12, hc25, hlam, hphi, p2849_1]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [h2847, hlam, p2849_0]
              · have p2849_0 := h2849c.1
                have p2849_1 := h2849c.2.1
                have p2849_2 := h2849c.2.2.1
                have p2849_3 := h2849c.2.2.2
                linarith only [hlam, p2849_0]
            · linarith only [h0, h2, h2782, h2848, h5, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2904 | h2904
            · linarith only [h1464, h2847, h2904, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h0, h2, h2782, h2904, h5, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1464 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1586 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 4 (by decide) (by decide) with h1647 | h1647
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h1464 h1586 h1647
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h1464 h1586 h1647

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1464 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 5 (by decide) (by decide) with h1586 | h1586
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h1464 h1586
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h1464 h1586

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 4 (by decide) (by decide) with h1464 | h1464
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h1464
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h1464

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8

set_option maxHeartbeats 5802000 in
set_option maxHeartbeats 5802000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s6 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7
  · linarith only [h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]

set_option maxHeartbeats 5806000 in
set_option maxHeartbeats 5806000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s5 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s6 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6
  · linarith only [h6, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s4 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s5 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5
  · linarith only [h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]

set_option maxHeartbeats 5814000 in
set_option maxHeartbeats 5814000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s3 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s4 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · linarith only [h4, hc25, hlam, hphi, ht01, ht12, u0ehi1]

set_option maxHeartbeats 5818000 in
set_option maxHeartbeats 5818000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s2 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s3 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · linarith only [h2, h3, hc24, hlam, hphi, ht01, ht12, u0ehi2]

set_option maxHeartbeats 5822000 in
set_option maxHeartbeats 5822000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s2 m hb0 hb2 hb3 hb5 h0 h1 h2
  · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]

set_option maxHeartbeats 5826000 in
set_option maxHeartbeats 5826000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s1 m hb0 hb2 hb3 hb5 h0 h1
  · linarith only [h1, hc13, hlam, hphi, ht01, u0ehi0]

set_option maxHeartbeats 5830000 in
set_option maxHeartbeats 5830000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s0 m hb0 hb2 hb3 hb5 h0
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

end R2N4
