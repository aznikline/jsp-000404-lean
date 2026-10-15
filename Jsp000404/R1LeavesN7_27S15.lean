import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_27S13
import Jsp000404.R1LeavesN7_27S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1865 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h2070 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 4 5 (by decide) (by decide) with h2489 | h2489
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2490 | h2490
    · linarith only [h0, h2, h2490, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2492 | h2492
      · linarith only [h1865, h2490, h2492, hc02, hc24, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2494 | h2494
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2495 | h2495
          · linarith only [h1, h2070, h2495, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2497 | h2497
            · linarith only [h2494, h2495, h2497, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2499 | h2499
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2500 | h2500
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2501 | h2501
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2502 | h2502
                    · linarith only [h2490, h2494, h2497, h2502, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h2489, h2494, h2495, h2502, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h0, h2, h2489, h2501, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h2, h2489, h2490, h2497, h2499, h2500, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h0, h2489, h2494, h2497, h2499, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2508 | h2508
          · linarith only [h2070, h2494, h2508, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2510 | h2510
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2511 | h2511
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2512 | h2512
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2513 | h2513
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2514 | h2514
                    · rcases h5bigk with h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [hlam, p2515_0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h1, h2508, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2515_1, u1elo0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h1865, hlam, p2515_0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h2070, hlam, p2515_1]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht5b, p2515_1, u1elo0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h1, hlam, p2515_0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [hlam, p2515_0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h2492, hlam, p2515_0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h2508, hlam, p2515_1]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p2515_1, u1elo4]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h1865, h2513, hc02, hc24, hlam, hphi, p2515_1]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h2492, h2513, hc12, hc24, hlam, hphi, p2515_1]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [hlam, p2515_0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h2070, h2511, h2513, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2515_1]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        rcases p2515_3 (m.d 0 5) (by simp) with h2530 | h2530
                        · linarith only [h1865, h2530, hlam]
                        · linarith only [h2489, h2530, hlam]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h1, h2492, hc12, hc35, hlam, hphi, ht23, p2515_1]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h2492, hc12, hc35, hlam, hphi, ht23, p2515_1]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h2512, hlam, p2515_0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [hlam, p2515_0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h2511, h2514, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2515_1]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h2489, hlam, p2515_0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h2510, hlam, p2515_0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h2513, hlam, p2515_0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [h2514, hlam, p2515_0]
                      · have p2515_0 := h2515c.1
                        have p2515_1 := h2515c.2.1
                        have p2515_2 := h2515c.2.2.1
                        have p2515_3 := h2515c.2.2.2
                        linarith only [hlam, p2515_0]
                    · linarith only [h0, h2489, h2494, h2514, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h2510, h2513, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h2494, h2511, h2512, hc13, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2546 | h2546
                · linarith only [h2070, h2511, h2546, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2548 | h2548
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2549 | h2549
                    · rcases h5bigk with h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c | h2550c
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [hlam, p2550_0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h0, h2489, h2492, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2550_1, u1elo0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h1865, hlam, p2550_0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h2070, hlam, p2550_1]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h0, h2489, hc45, hlam, hphi, ht01, ht0b, ht5b, p2550_1, u1elo0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h1, hlam, p2550_0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [hlam, p2550_0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h2492, hlam, p2550_0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h2508, hlam, p2550_1]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p2550_1, u1elo4]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h1865, h2546, hc02, hc35, hlam, hphi, ht23, p2550_1]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h2492, h2546, hc12, hc35, hlam, hphi, ht23, p2550_1]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [hlam, p2550_0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h2546, hlam, p2550_1]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        rcases p2550_3 (m.d 0 5) (by simp) with h2565 | h2565
                        · linarith only [h1865, h2565, hlam]
                        · linarith only [h2489, h2565, hlam]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h1, h2492, h2549, hc12, hc34, hlam, hphi, ht23, p2550_1]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h2492, h2549, hc12, hc34, hlam, hphi, ht23, p2550_1]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h1865, h2549, hc02, hc34, hlam, hphi, ht23, p2550_1]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [hlam, p2550_0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        rcases p2550_3 (m.d 0 5) (by simp) with h2572 | h2572
                        · linarith only [h2070, h2572, hlam]
                        · linarith only [h2489, h2572, hlam]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h2489, hlam, p2550_0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h2510, hlam, p2550_0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h2548, hlam, p2550_0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [h2549, hlam, p2550_0]
                      · have p2550_0 := h2550c.1
                        have p2550_1 := h2550c.2.1
                        have p2550_2 := h2550c.2.2.1
                        have p2550_3 := h2550c.2.2.2
                        linarith only [hlam, p2550_0]
                    · linarith only [h0, h2489, h2494, h2549, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h2, h2510, h2548, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2582 | h2582
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2583 | h2583
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2584 | h2584
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2585 | h2585
                    · linarith only [h2490, h2510, h2582, h2585, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h2489, h2494, h2585, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h2, h2489, h2584, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h2494, h2582, h2583, hc13, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2590 | h2590
                · linarith only [h2070, h2582, h2590, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2592 | h2592
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2593 | h2593
                    · rcases h5bigk with h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c | h2594c
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [hlam, p2594_0]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h1865, h2490, h2510, hc12, hc25, hlam, hphi, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h1865, hlam, p2594_0]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2070, hlam, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h0, h2489, hc45, hlam, hphi, ht01, ht0b, ht5b, p2594_1, u1elo0]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h1, hlam, p2594_0]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [hlam, p2594_0]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2492, hlam, p2594_0]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2508, hlam, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2510, hlam, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h1, h2490, h2510, h2590, hc12, hc35, hlam, hphi, ht23, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2490, h2510, h2590, hc12, hc35, hlam, hphi, ht23, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [hlam, p2594_0]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2590, hlam, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2490, h2510, h2592, hc12, hc24, hlam, hphi, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2489, h2490, h2510, hc12, hc35, hlam, hphi, ht23, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2490, h2510, hc12, hc35, hlam, hphi, ht23, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h1865, hc02, hc35, hlam, hphi, ht23, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [hlam, p2594_0]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2490, h2510, h2593, hc12, hc34, hlam, hphi, ht23, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2489, hlam, p2594_0]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h1865, h2489, h2490, h2510, hc12, hc25, hlam, hphi, p2594_1]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2592, hlam, p2594_0]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [h2593, hlam, p2594_0]
                      · have p2594_0 := h2594c.1
                        have p2594_1 := h2594c.2.1
                        have p2594_2 := h2594c.2.2.1
                        have p2594_3 := h2594c.2.2.2
                        linarith only [hlam, p2594_0]
                    · linarith only [h0, h2, h2489, h2582, h2593, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h2, h2489, h2592, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2622 | h2622
    · linarith only [h0, h2, h2622, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2624 | h2624
      · linarith only [h1865, h2622, h2624, hc02, hc24, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2626 | h2626
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2627 | h2627
          · linarith only [h1, h2070, h2627, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2629 | h2629
            · linarith only [h0, h2489, h2629, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2631 | h2631
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2632 | h2632
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2633 | h2633
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2634 | h2634
                    · linarith only [h1, h2489, h2626, h2627, h2634, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · rcases h5bigk with h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [hlam, p2636_0]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2070, h2631, h2633, h2634, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h1865, hlam, p2636_0]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2070, hlam, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2489, hlam, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h1, hlam, p2636_0]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [hlam, p2636_0]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2624, hlam, p2636_0]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2627, hlam, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2629, hlam, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h1865, hc02, hc25, hlam, hphi, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2624, hc12, hc25, hlam, hphi, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [hlam, p2636_0]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2626, h2627, h2632, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h0, h2489, h2622, h2631, h2633, hc12, hc23, hlam, hphi, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h1, h2626, h2627, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2626, h2627, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2632, hlam, p2636_0]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [hlam, p2636_0]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2634, hlam, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h1, h2626, h2627, hc34, hc45, hlam, hphi, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2626, h2627, hc34, hc45, hlam, hphi, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2633, hlam, p2636_0]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [h2631, h2633, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2636_1]
                      · have p2636_0 := h2636c.1
                        have p2636_1 := h2636c.2.1
                        have p2636_2 := h2636c.2.2.1
                        have p2636_3 := h2636c.2.2.2
                        linarith only [hlam, p2636_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2662 | h2662
                    · linarith only [h2626, h2633, h2662, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases h5bigk with h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [hlam, p2664_0]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2626, h2627, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h1865, hlam, p2664_0]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2070, hlam, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2489, hlam, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h1, hlam, p2664_0]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [hlam, p2664_0]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2624, hlam, p2664_0]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2627, hlam, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2629, hlam, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h1, h2626, h2627, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2626, h2627, h2633, hc34, hc45, hlam, hphi, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [hlam, p2664_0]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2626, h2627, h2633, hc34, hc45, hlam, hphi, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2633, hlam, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h1, h2626, h2627, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2626, h2627, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2632, hlam, p2664_0]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [hlam, p2664_0]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2662, hlam, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h1, h2626, h2627, hc34, hc45, hlam, hphi, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2626, h2627, hc34, hc45, hlam, hphi, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h1865, hc02, hc45, hlam, hphi, ht23, ht34, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [h2070, hc03, hc45, hlam, hphi, ht34, p2664_1]
                      · have p2664_0 := h2664c.1
                        have p2664_1 := h2664c.2.1
                        have p2664_2 := h2664c.2.2.1
                        have p2664_3 := h2664c.2.2.2
                        linarith only [hlam, p2664_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2690 | h2690
                  · linarith only [h0, h2489, h2622, h2631, h2632, h2690, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2692 | h2692
                    · linarith only [h2626, h2690, h2692, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases h5bigk with h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c | h2694c
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [hlam, p2694_0]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h1, h2627, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2694_1, u1elo0]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h1865, hlam, p2694_0]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2070, hlam, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2489, hlam, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h1, hlam, p2694_0]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [hlam, p2694_0]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2624, hlam, p2694_0]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2627, hlam, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2629, hlam, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h1865, hc02, hc25, hlam, hphi, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2624, hc12, hc25, hlam, hphi, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [hlam, p2694_0]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2632, hlam, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2690, hlam, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h0, h2489, h2622, h2692, hc12, hc45, hlam, hphi, ht23, ht34, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2624, h2692, hc12, hc45, hlam, hphi, ht23, ht34, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h1865, h2692, hc02, hc45, hlam, hphi, ht23, ht34, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [hlam, p2694_0]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2692, hlam, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h1, h2627, hc13, hc45, hlam, hphi, ht34, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2626, h2627, hc34, hc45, hlam, hphi, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2, h2631, h2632, hc02, hc45, hlam, hphi, ht23, ht34, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [h2070, hc03, hc45, hlam, hphi, ht34, p2694_1]
                      · have p2694_0 := h2694c.1
                        have p2694_1 := h2694c.2.1
                        have p2694_2 := h2694c.2.2.1
                        have p2694_3 := h2694c.2.2.2
                        linarith only [hlam, p2694_0]
              · linarith only [h2626, h2627, h2631, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2721 | h2721
          · linarith only [h2070, h2626, h2721, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2723 | h2723
            · linarith only [h0, h2489, h2723, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2725 | h2725
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2726 | h2726
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2727 | h2727
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2728 | h2728
                    · linarith only [h0, h2489, h2622, h2725, h2728, hc12, hc23, hlam, hphi]
                    · rcases h5bigk with h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c | h2730c
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [hlam, p2730_0]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p2730_1, u1elo0]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h1865, hlam, p2730_0]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2070, hlam, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2489, hlam, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h1, hlam, p2730_0]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [hlam, p2730_0]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2624, hlam, p2730_0]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2721, hlam, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2723, hlam, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h1865, hc02, hc25, hlam, hphi, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2624, hc12, hc25, hlam, hphi, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [hlam, p2730_0]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2626, h2726, h2728, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h0, h2489, h2622, h2725, h2727, hc12, hc23, hlam, hphi, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h0, h2489, h2622, hc12, hc35, hlam, hphi, ht23, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2622, h2723, hc12, hc35, hlam, hphi, ht23, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2726, hlam, p2730_0]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [hlam, p2730_0]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2728, hlam, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h0, h2489, h2622, hc12, hc45, hlam, hphi, ht23, ht34, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2622, h2723, hc12, hc45, hlam, hphi, ht23, ht34, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2727, hlam, p2730_0]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [h2725, h2727, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2730_1]
                      · have p2730_0 := h2730c.1
                        have p2730_1 := h2730c.2.1
                        have p2730_2 := h2730c.2.2.1
                        have p2730_3 := h2730c.2.2.2
                        linarith only [hlam, p2730_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2756 | h2756
                    · linarith only [h2, h2727, h2756, hc02, hc34, hlam, hphi, ht23]
                    · rcases h5bigk with h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [hlam, p2758_0]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h1, h2622, h2723, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2758_1, u1elo0]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h1865, hlam, p2758_0]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2070, hlam, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2489, hlam, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h1, hlam, p2758_0]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [hlam, p2758_0]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2624, hlam, p2758_0]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2721, hlam, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2723, hlam, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h1, h2622, h2723, hc12, hc25, hlam, hphi, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2622, h2723, h2727, hc12, hc45, hlam, hphi, ht23, ht34, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [hlam, p2758_0]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2626, h2727, h2756, hc13, hc45, hlam, hphi, ht34, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2727, hlam, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h1, h2622, h2723, hc12, hc35, hlam, hphi, ht23, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2622, h2723, hc12, hc35, hlam, hphi, ht23, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2726, hlam, p2758_0]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [hlam, p2758_0]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2756, hlam, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h1, h2622, h2723, hc12, hc45, hlam, hphi, ht23, ht34, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2622, h2723, hc12, hc45, hlam, hphi, ht23, ht34, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h1865, hc02, hc45, hlam, hphi, ht23, ht34, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [h2070, hc03, hc45, hlam, hphi, ht34, p2758_1]
                      · have p2758_0 := h2758c.1
                        have p2758_1 := h2758c.2.1
                        have p2758_2 := h2758c.2.2.1
                        have p2758_3 := h2758c.2.2.2
                        linarith only [hlam, p2758_0]
                · linarith only [h2626, h2725, h2726, hc13, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2785 | h2785
                · linarith only [h2070, h2725, h2785, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2787 | h2787
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2788 | h2788
                    · rcases h5bigk with h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c | h2789c
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [hlam, p2789_0]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h1, h2622, h2723, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2789_1, u1elo0]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h1865, hlam, p2789_0]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h2070, hlam, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h2489, hlam, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h1, hlam, p2789_0]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [hlam, p2789_0]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h2624, hlam, p2789_0]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h2721, hlam, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h2723, hlam, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h1, h2622, h2723, hc12, hc25, hlam, hphi, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h2622, h2723, h2785, hc12, hc35, hlam, hphi, ht23, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [hlam, p2789_0]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h2785, hlam, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h2489, h2725, h2787, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h1, h2622, h2723, hc12, hc35, hlam, hphi, ht23, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h2622, h2723, hc12, hc35, hlam, hphi, ht23, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h1865, hc02, hc35, hlam, hphi, ht23, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [hlam, p2789_0]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h0, h2489, h2622, h2788, hc12, hc34, hlam, hphi, ht23, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h1, h2622, h2723, h2787, hc12, hc25, hlam, hphi, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h2622, h2723, hc12, hc45, hlam, hphi, ht23, ht34, p2789_1]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h2787, hlam, p2789_0]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [h2788, hlam, p2789_0]
                      · have p2789_0 := h2789c.1
                        have p2789_1 := h2789c.2.1
                        have p2789_2 := h2789c.2.2.1
                        have p2789_3 := h2789c.2.2.2
                        linarith only [hlam, p2789_0]
                    · linarith only [h2725, h2787, h2788, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2816 | h2816
                    · linarith only [h2, h2787, h2816, hc02, hc34, hlam, hphi, ht23]
                    · rcases h5bigk with h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [hlam, p2818_0]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h1, h2622, h2723, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2818_1, u1elo0]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h1865, hlam, p2818_0]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h2070, hlam, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h2489, hlam, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h1, hlam, p2818_0]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [hlam, p2818_0]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h2624, hlam, p2818_0]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h2721, hlam, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h2723, hlam, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h1, h2622, h2723, h2785, h2816, hc12, hc45, hlam, hphi, ht23, ht34, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h2622, h2723, h2785, h2816, hc12, hc45, hlam, hphi, ht23, ht34, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [hlam, p2818_0]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h2785, hlam, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h2787, hlam, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h1, h2622, h2723, h2816, hc12, hc45, hlam, hphi, ht23, ht34, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h2622, h2723, h2816, hc12, hc45, hlam, hphi, ht23, ht34, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h1865, h2816, hc02, hc45, hlam, hphi, ht23, ht34, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [hlam, p2818_0]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h2816, hlam, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h1, h2622, h2723, hc12, hc45, hlam, hphi, ht23, ht34, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h2622, h2723, hc12, hc45, hlam, hphi, ht23, ht34, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h1865, hc02, hc45, hlam, hphi, ht23, ht34, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [h2070, hc03, hc45, hlam, hphi, ht34, p2818_1]
                      · have p2818_0 := h2818c.1
                        have p2818_1 := h2818c.2.1
                        have p2818_2 := h2818c.2.2.1
                        have p2818_3 := h2818c.2.2.2
                        linarith only [hlam, p2818_0]

set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1865 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 5 (by decide) (by decide) with h2070 | h2070
  · exact r1l7_11_25_L_0_H_I_s1_x1_x1_x0 m hb1 hb5 hg0 hg1 h2 h1865 h2070
  · exact r1l7_11_25_L_0_H_I_s1_x1_x1_x1 m hb1 hb5 hg0 hg1 h2 h1865 h2070

set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h1865 | h1865
  · exact r1l7_11_25_L_0_H_I_s1_x1_x0 m hb1 hb5 hg0 hg1 h2 h1865
  · exact r1l7_11_25_L_0_H_I_s1_x1_x1 m hb1 hb5 hg0 hg1 h2 h1865

set_option maxHeartbeats 5684000 in
set_option maxHeartbeats 5684000 in
theorem r1l7_11_25_L_0_H_I_s1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_25_L_0_H_I_s1_x0 m hb1 hb5 hg0 hg1 h2
  · exact r1l7_11_25_L_0_H_I_s1_x1 m hb1 hb5 hg0 hg1 h2

end R2N4
