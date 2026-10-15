import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_49S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h2492 | h2492
  · linarith only [h0, h2492, hc12, hlam, hphi, u1ehi2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2494 | h2494
    · linarith only [h0, h2494, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2496 | h2496
      · linarith only [h0, h2496, hc12, hlam, hphi, u1ehi4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2498 | h2498
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2499 | h2499
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2500 | h2500
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2501 | h2501
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2502 | h2502
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2503 | h2503
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2504 | h2504
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2505 | h2505
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2506 | h2506
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2507 | h2507
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2508 | h2508
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2509 | h2509
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2510 | h2510
                                · rcases h1bigk with h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c | h2511c
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h0, hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2492, hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2494, hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2496, hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2511_1, u1ehi0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2496, h2504, h2506, hc12, hlam, hphi, p2511_1, u1ehi0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2496, h2506, hc12, hlam, hphi, p2511_1, u1ehi0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2496, hc12, hlam, hphi, p2511_1, u1ehi0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [hc13, hlam, hphi, p2511_1, u1ehi0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2501, hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2496, h2501, h2506, hc12, hlam, hphi, p2511_1, u1ehi0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2496, h2501, hc12, hlam, hphi, p2511_1, u1ehi0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [hc14, hlam, hphi, p2511_1, u1ehi0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2502, hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2504, hlam, p2511_1]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2496, h2501, h2504, hc12, hlam, hphi, p2511_1, u1ehi0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [hc15, hlam, hphi, p2511_1, u1ehi0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2503, hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2505, hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [h2506, hlam, p2511_0]
                                  · have p2511_0 := h2511c.1
                                    have p2511_1 := h2511c.2.1
                                    have p2511_2 := h2511c.2.2.1
                                    have p2511_3 := h2511c.2.2.2
                                    linarith only [hlam, p2511_0]
                                · rcases h1bigk with h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c | h2537c
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h0, hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2492, hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2494, hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2496, hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2537_1, u1ehi0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2537_1, u1ehi2]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2494, hc12, hlam, hphi, p2537_1, u1ehi0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2496, hc12, hlam, hphi, p2537_1, u1ehi0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [hc13, hlam, hphi, p2537_1, u1ehi0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2501, hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2494, h2501, hc12, hlam, hphi, p2537_1, u1ehi0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2496, h2501, hc12, hlam, hphi, p2537_1, u1ehi0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [hc14, hlam, hphi, p2537_1, u1ehi0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2502, hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2504, hlam, p2537_1]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2496, h2501, h2504, hc12, hlam, hphi, p2537_1, u1ehi0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [hc15, hlam, hphi, p2537_1, u1ehi0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2503, hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2505, hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [h2506, hlam, p2537_0]
                                  · have p2537_0 := h2537c.1
                                    have p2537_1 := h2537c.2.1
                                    have p2537_2 := h2537c.2.2.1
                                    have p2537_3 := h2537c.2.2.2
                                    linarith only [hlam, p2537_0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2563 | h2563
                                · linarith only [h2501, h2507, h2509, h2563, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h1bigk with h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h0, hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2492, hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2494, hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2496, hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2565_1, u1ehi0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2565_1, u1ehi2]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2494, hc12, hlam, hphi, p2565_1, u1ehi0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2496, hc12, hlam, hphi, p2565_1, u1ehi0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [hc13, hlam, hphi, p2565_1, u1ehi0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2501, hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2501, hc12, hlam, hphi, p2565_1, u1ehi3]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2496, h2501, hc12, hlam, hphi, p2565_1, u1ehi0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [hc14, hlam, hphi, p2565_1, u1ehi0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2502, hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2504, hlam, p2565_1]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2496, h2501, h2504, hc12, hlam, hphi, p2565_1, u1ehi0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [hc15, hlam, hphi, p2565_1, u1ehi0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2503, hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2505, hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [h2506, hlam, p2565_0]
                                  · have p2565_0 := h2565c.1
                                    have p2565_1 := h2565c.2.1
                                    have p2565_2 := h2565c.2.2.1
                                    have p2565_3 := h2565c.2.2.2
                                    linarith only [hlam, p2565_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2591 | h2591
                              · linarith only [h2507, h2508, h2591, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2593 | h2593
                                · linarith only [h2501, h2505, h2507, h2508, h2591, h2593, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h1bigk with h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c | h2595c
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h0, hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2492, hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2494, hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2496, hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2595_1, u1ehi0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2492, h2499, h2500, h2508, h2593, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2595_1]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2496, h2506, hc12, hlam, hphi, p2595_1, u1ehi0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2496, hc12, hlam, hphi, p2595_1, u1ehi0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [hc13, hlam, hphi, p2595_1, u1ehi0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2501, hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2496, h2501, h2506, hc12, hlam, hphi, p2595_1, u1ehi0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2496, h2501, hc12, hlam, hphi, p2595_1, u1ehi0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [hc14, hlam, hphi, p2595_1, u1ehi0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2502, hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2504, hlam, p2595_1]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2496, h2501, h2504, hc12, hlam, hphi, p2595_1, u1ehi0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [hc15, hlam, hphi, p2595_1, u1ehi0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2503, hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2505, hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [h2506, hlam, p2595_0]
                                  · have p2595_0 := h2595c.1
                                    have p2595_1 := h2595c.2.1
                                    have p2595_2 := h2595c.2.2.1
                                    have p2595_3 := h2595c.2.2.2
                                    linarith only [hlam, p2595_0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2621 | h2621
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2622 | h2622
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2623 | h2623
                                · rcases h1bigk with h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c | h2624c
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h0, hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2492, hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2494, hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2496, hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2624_1, u1ehi0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2492, h2499, h2507, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2624_1]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2624_1, u1ehi3]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2496, hc12, hlam, hphi, p2624_1, u1ehi0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [hc13, hlam, hphi, p2624_1, u1ehi0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2501, hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2494, h2501, hc12, hlam, hphi, p2624_1, u1ehi0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2496, h2501, hc12, hlam, hphi, p2624_1, u1ehi0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [hc14, hlam, hphi, p2624_1, u1ehi0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2502, hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2504, hlam, p2624_1]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2496, h2501, h2504, hc12, hlam, hphi, p2624_1, u1ehi0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [hc15, hlam, hphi, p2624_1, u1ehi0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2503, hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2505, hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [h2506, hlam, p2624_0]
                                  · have p2624_0 := h2624c.1
                                    have p2624_1 := h2624c.2.1
                                    have p2624_2 := h2624c.2.2.1
                                    have p2624_3 := h2624c.2.2.2
                                    linarith only [hlam, p2624_0]
                                · linarith only [h2500, h2507, h2621, h2623, hc04, hc35, hlam, hphi, ht0b, ht5b]
                              · linarith only [h2507, h2621, h2622, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2652 | h2652
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2653 | h2653
                                · rcases h1bigk with h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c | h2654c
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h0, hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2492, hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2494, hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2496, hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2654_1, u1ehi0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2654_1, u1ehi2]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2494, hc12, hlam, hphi, p2654_1, u1ehi0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2496, hc12, hlam, hphi, p2654_1, u1ehi0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [hc13, hlam, hphi, p2654_1, u1ehi0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2501, hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2494, h2501, hc12, hlam, hphi, p2654_1, u1ehi0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2496, h2501, hc12, hlam, hphi, p2654_1, u1ehi0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [hc14, hlam, hphi, p2654_1, u1ehi0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2502, hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2504, hlam, p2654_1]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2496, h2501, h2504, hc12, hlam, hphi, p2654_1, u1ehi0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [hc15, hlam, hphi, p2654_1, u1ehi0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2503, hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2505, hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [h2506, hlam, p2654_0]
                                  · have p2654_0 := h2654c.1
                                    have p2654_1 := h2654c.2.1
                                    have p2654_2 := h2654c.2.2.1
                                    have p2654_3 := h2654c.2.2.2
                                    linarith only [hlam, p2654_0]
                                · linarith only [h2507, h2652, h2653, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2681 | h2681
                                · rcases h1bigk with h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c | h2682c
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h0, hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2492, hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2494, hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2496, hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2682_1, u1ehi0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2492, h2499, h2507, h2652, h2681, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2682_1]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2682_1, u1ehi3]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2496, hc12, hlam, hphi, p2682_1, u1ehi0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [hc13, hlam, hphi, p2682_1, u1ehi0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2501, hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2494, h2501, hc12, hlam, hphi, p2682_1, u1ehi0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2496, h2501, hc12, hlam, hphi, p2682_1, u1ehi0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [hc14, hlam, hphi, p2682_1, u1ehi0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2502, hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2504, hlam, p2682_1]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2496, h2501, h2504, hc12, hlam, hphi, p2682_1, u1ehi0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [hc15, hlam, hphi, p2682_1, u1ehi0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2503, hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2505, hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [h2506, hlam, p2682_0]
                                  · have p2682_0 := h2682c.1
                                    have p2682_1 := h2682c.2.1
                                    have p2682_2 := h2682c.2.2.1
                                    have p2682_3 := h2682c.2.2.2
                                    linarith only [hlam, p2682_0]
                                · rcases h1bigk with h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h0, hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2492, hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2494, hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2496, hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2708_1, u1ehi0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [hc12, hlam, hphi, p2708_1, u1ehi2]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2494, h2500, h2507, h2681, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2708_1]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2496, hc12, hlam, hphi, p2708_1, u1ehi0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [hc13, hlam, hphi, p2708_1, u1ehi0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2501, hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2494, h2500, h2501, h2507, h2681, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2708_1]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2496, h2501, hc12, hlam, hphi, p2708_1, u1ehi0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [hc14, hlam, hphi, p2708_1, u1ehi0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2502, hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2504, hlam, p2708_1]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2496, h2501, h2504, hc12, hlam, hphi, p2708_1, u1ehi0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [hc15, hlam, hphi, p2708_1, u1ehi0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2503, hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2505, hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [h2506, hlam, p2708_0]
                                  · have p2708_0 := h2708c.1
                                    have p2708_1 := h2708c.2.1
                                    have p2708_2 := h2708c.2.2.1
                                    have p2708_3 := h2708c.2.2.2
                                    linarith only [hlam, p2708_0]
                        · linarith only [h2492, h2499, h2500, h2501, h2506, hc12, hlam, hphi, u1ehi3]
                      · linarith only [h2492, h2505, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h2492, h2504, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h2492, h2501, h2503, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h2492, h2501, h2502, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h2501, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2740 | h2740
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2741 | h2741
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2742 | h2742
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2743 | h2743
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2744 | h2744
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2745 | h2745
                        · linarith only [h2494, h2500, h2740, h2743, h2745, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h2494, h2745, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                      · linarith only [h2492, h2744, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h2492, h2743, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h0, h2742, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h2492, h2498, h2740, h2741, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
              · linarith only [h0, h2740, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2753 | h2753
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2754 | h2754
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2755 | h2755
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2756 | h2756
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2757 | h2757
                    · linarith only [h2492, h2499, h2754, h2757, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h2492, h2757, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h0, h2756, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h2498, h2755, hlam]
              · linarith only [h0, h2754, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2763 | h2763
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2764 | h2764
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2765 | h2765
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2766 | h2766
                    · linarith only [h2492, h2499, h2763, h2766, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h2492, h2766, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h0, h2765, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h2498, h2764, hlam]
              · linarith only [h0, h2763, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2772 | h2772
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2773 | h2773
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2774 | h2774
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2775 | h2775
                · linarith only [h0, h2498, h2775, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h2775, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h2774, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2779 | h2779
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2780 | h2780
                · linarith only [h0, h2498, h2780, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h2780, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h2779, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2784 | h2784
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2785 | h2785
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2786 | h2786
                · linarith only [h0, h2498, h2786, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h2786, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h2785, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2790 | h2790
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2791 | h2791
                · linarith only [h0, h2498, h2791, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h2791, hc24, hlam, hphi, ht12, u1ehi0]
              · linarith only [h0, h2790, hc23, hlam, hphi, ht12, u1ehi0]

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_14_M_IR_L_I_x0 m hb1 hb4 h0
  · exact r1l7_21_14_M_IR_L_I_x1 m hb1 hb4 h0

end R2N4
