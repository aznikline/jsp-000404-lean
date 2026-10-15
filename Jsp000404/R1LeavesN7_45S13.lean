import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_45S11
import Jsp000404.R1LeavesN7_45S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1647 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2158 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2377 | h2377
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2378 | h2378
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2379 | h2379
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2380 | h2380
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2381 | h2381
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2382 | h2382
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2383 | h2383
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2384 | h2384
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2385 | h2385
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2386 | h2386
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2387 | h2387
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2388 | h2388
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2389 | h2389
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2390 | h2390
                            · linarith only [h2378, h2388, h2390, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · linarith only [h0, h2377, h2386, h2389, h2390, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2393 | h2393
                            · linarith only [h2388, h2389, h2393, hlam]
                            · rcases h0bigk with h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c | h2395c
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [hlam, p2395_0]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h0, hlam, p2395_0]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h1647, hlam, p2395_0]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h2158, hlam, p2395_0]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h1647, h2384, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2395_1, u2elo1]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2395_1, u2elo1]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [hlam, p2395_0]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h0, h2381, h2383, h2388, h2389, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2395_1, u2elo1]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h0, h2383, h2388, h2389, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2395_1, u2elo1]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h0, h2377, h2386, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2395_1, u2elo1]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h2377, h2386, hc03, hc25, hlam, hphi, ht0b, ht5b, p2395_1]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h2378, hlam, p2395_0]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [hlam, p2395_0]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h1647, h2383, h2384, h2388, h2389, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2395_1, u2elo1]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h1647, h2377, h2384, h2386, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2395_1, u2elo1]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h2377, h2386, hc04, hc25, hlam, hphi, ht0b, ht5b, p2395_1]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h2379, hlam, p2395_0]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h2381, hlam, p2395_1]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [hlam, p2395_0]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h1647, h2377, h2381, h2384, h2386, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2395_1, u2elo1]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h2377, hlam, p2395_1]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h2380, hlam, p2395_0]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h2382, hlam, p2395_0]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [h2383, hlam, p2395_0]
                              · have p2395_0 := h2395c.1
                                have p2395_1 := h2395c.2.1
                                have p2395_2 := h2395c.2.2.1
                                have p2395_3 := h2395c.2.2.2
                                linarith only [hlam, p2395_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2421 | h2421
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2422 | h2422
                            · rcases h0bigk with h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c | h2423c
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [hlam, p2423_0]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h0, hlam, p2423_0]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h1647, hlam, p2423_0]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h2158, hlam, p2423_0]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h0, h2377, h2386, h2421, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2423_1, u2elo1]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2423_1, u2elo1]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [hlam, p2423_0]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2423_1, u2elo1]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2423_1, u2elo1]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h0, h2377, h2386, h2421, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2423_1, u2elo1]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h2377, h2386, h2421, hc03, hc45, hlam, hphi, ht0b, ht5b, p2423_1]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h2378, hlam, p2423_0]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [hlam, p2423_0]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h1647, h2158, h2377, h2384, h2386, h2421, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2423_1, u2elo1]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h1647, h2377, h2384, h2386, h2421, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2423_1, u2elo1]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h2377, h2386, h2421, hc04, hc45, hlam, hphi, ht0b, ht5b, p2423_1]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h2379, hlam, p2423_0]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h2381, hlam, p2423_1]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [hlam, p2423_0]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h1647, h2377, h2381, h2384, h2386, h2421, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2423_1, u2elo1]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h2377, hlam, p2423_1]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h2380, hlam, p2423_0]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h2382, hlam, p2423_0]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [h2383, hlam, p2423_0]
                              · have p2423_0 := h2423c.1
                                have p2423_1 := h2423c.2.1
                                have p2423_2 := h2423c.2.2.1
                                have p2423_3 := h2423c.2.2.2
                                linarith only [hlam, p2423_0]
                            · linarith only [h2388, h2421, h2422, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2450 | h2450
                            · linarith only [h1647, h2381, h2384, h2388, h2421, h2450, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h1647, h2377, h2383, h2384, h2388, h2450, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1647, h2382, h2387, hlam]
                    · linarith only [h1647, h2384, h2386, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1647, h2384, h2385, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2377, h2384, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h2158, h2377, h2383, hlam]
            · linarith only [h1647, h2377, h2382, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2459 | h2459
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2460 | h2460
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2461 | h2461
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2462 | h2462
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2463 | h2463
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2464 | h2464
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2465 | h2465
                        · linarith only [h1647, h2381, h2465, hc01, hlam, hphi, ht12, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2467 | h2467
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2468 | h2468
                            · rcases h0bigk with h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c | h2469c
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h0, hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h1647, hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h2158, hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h1647, h2461, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2469_1]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2469_1, u2elo1]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2469_1, u2elo1]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h0, h1647, h2377, h2381, h2463, h2467, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2469_1, u2elo1]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h0, h2377, h2463, h2467, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2469_1, u2elo1]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h2377, h2463, h2467, hc03, hc45, hlam, hphi, ht0b, ht5b, p2469_1]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h2378, hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h2381, hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h2377, h2381, h2463, h2467, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2469_1]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h0, h2377, h2379, h2463, h2467, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2469_1, u2elo1]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h2379, hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h0, h2379, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2469_1, u2elo1]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h0, h2377, h2379, h2463, h2467, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2469_1, u2elo1]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h2377, hlam, p2469_1]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h2380, hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h2459, hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [h2460, hlam, p2469_0]
                              · have p2469_0 := h2469c.1
                                have p2469_1 := h2469c.2.1
                                have p2469_2 := h2469c.2.2.1
                                have p2469_3 := h2469c.2.2.2
                                linarith only [hlam, p2469_0]
                            · linarith only [h0, h2377, h2463, h2467, h2468, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2496 | h2496
                            · linarith only [h1647, h2377, h2461, h2464, h2465, h2467, h2496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h2381, h2460, h2496, hlam]
                      · linarith only [h2381, h2459, h2464, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h2463, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1647, h2461, h2462, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2378, h2461, hlam]
              · linarith only [h1647, h2377, h2381, h2460, hlam]
            · linarith only [h1647, h2377, h2459, hlam]
        · linarith only [h0, h2377, h2380, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2506 | h2506
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2507 | h2507
          · linarith only [h2378, h2379, h2507, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2509 | h2509
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2510 | h2510
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2511 | h2511
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2512 | h2512
                  · linarith only [h1647, h2378, h2379, h2512, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h2377, h2512, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h0, h2377, h2511, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h1647, h2377, h2378, h2379, h2510, hlam]
            · linarith only [h1647, h2377, h2509, hlam]
        · linarith only [h1647, h2377, h2378, h2506, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2519 | h2519
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2520 | h2520
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2521 | h2521
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2522 | h2522
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2523 | h2523
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2524 | h2524
                · linarith only [h2378, h2524, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h2377, h2524, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h2158, h2377, h2523, hlam]
            · linarith only [h2158, h2377, h2378, h2519, h2522, hlam]
          · linarith only [h2378, h2519, h2521, hlam]
        · linarith only [h2158, h2377, h2519, h2520, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2531 | h2531
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2532 | h2532
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2533 | h2533
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2534 | h2534
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2535 | h2535
                · linarith only [h0, h2377, h2378, h2535, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h2377, h2535, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h0, h2377, h2519, h2534, hlam]
            · linarith only [h0, h2377, h2519, h2532, h2533, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2540 | h2540
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2541 | h2541
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2542 | h2542
                · linarith only [h0, h2377, h2378, h2542, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h2377, h2542, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h1647, h2377, h2532, h2541, hlam]
            · linarith only [h0, h2377, h2378, h2540, hlam]
        · linarith only [h0, h2377, h2531, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2548 | h2548
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2549 | h2549
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2550 | h2550
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2551 | h2551
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2552 | h2552
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2553 | h2553
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2554 | h2554
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2555 | h2555
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2556 | h2556
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2557 | h2557
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2558 | h2558
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2559 | h2559
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2560 | h2560
                            · linarith only [h2548, h2558, h2560, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · linarith only [h0, h2548, h2558, h2559, h2560, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2563 | h2563
                            · linarith only [h0, h2548, h2551, h2559, h2563, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases h0bigk with h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c | h2565c
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
                                linarith only [h1647, hlam, p2565_0]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h2158, hlam, p2565_0]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h2377, hlam, p2565_0]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2565_1, u2elo1]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [hlam, p2565_0]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2565_1, u2elo1]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h0, h2377, h2553, hc01, hlam, hphi, ht12, p2565_1, u2elo1]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h0, h2377, hc01, hlam, hphi, ht12, p2565_1, u2elo1]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h1647, h2554, hc01, hlam, hphi, ht12, p2565_1, u2elo1]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h2548, hlam, p2565_0]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [hlam, p2565_0]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h1647, h2377, h2553, h2554, hc01, hlam, hphi, ht12, p2565_1, u2elo1]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h1647, h2377, h2554, hc01, hlam, hphi, ht12, p2565_1, u2elo1]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h2158, hc01, hc14, hlam, hphi, p2565_1]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h2549, hlam, p2565_0]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h2551, hlam, p2565_1]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [hlam, p2565_0]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h1647, h2377, h2551, h2554, hc01, hlam, hphi, ht12, p2565_1, u2elo1]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h2377, h2554, h2557, hc01, hlam, hphi, ht12, p2565_1, u2elo1]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h2550, hlam, p2565_0]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h2552, hlam, p2565_0]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [h2553, hlam, p2565_0]
                              · have p2565_0 := h2565c.1
                                have p2565_1 := h2565c.2.1
                                have p2565_2 := h2565c.2.2.1
                                have p2565_3 := h2565c.2.2.2
                                linarith only [hlam, p2565_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2591 | h2591
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2592 | h2592
                            · rcases h0bigk with h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c | h2593c
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h0, hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h1647, hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h2158, hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h2377, hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2593_1, u2elo1]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h0, h2551, h2558, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2593_1, u2elo1]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2593_1, u2elo1]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h0, h2377, hc01, hlam, hphi, ht12, p2593_1, u2elo1]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h1647, h2554, hc01, hlam, hphi, ht12, p2593_1, u2elo1]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h2548, hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h1647, h2549, h2554, h2591, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2593_1, u2elo1]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h1647, h2377, h2554, hc01, hlam, hphi, ht12, p2593_1, u2elo1]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h2158, h2555, hc01, hlam, hphi, ht12, p2593_1, u2elo1]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h2549, hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h2551, hlam, p2593_1]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h1647, h2377, h2551, h2554, hc01, hlam, hphi, ht12, p2593_1, u2elo1]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h2377, h2554, h2557, hc01, hlam, hphi, ht12, p2593_1, u2elo1]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h2550, hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h2552, hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [h2553, hlam, p2593_0]
                              · have p2593_0 := h2593c.1
                                have p2593_1 := h2593c.2.1
                                have p2593_2 := h2593c.2.2.1
                                have p2593_3 := h2593c.2.2.2
                                linarith only [hlam, p2593_0]
                            · linarith only [h2558, h2591, h2592, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2620 | h2620
                            · linarith only [h1647, h2551, h2554, h2591, h2620, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h1647, h2551, h2553, h2554, h2558, h2620, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1647, h2552, h2557, hlam]
                    · linarith only [h0, h2550, h2556, hlam]
                  · linarith only [h0, h2555, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2554, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2627 | h2627
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2628 | h2628
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2629 | h2629
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2630 | h2630
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2631 | h2631
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2632 | h2632
                          · linarith only [h2548, h2553, h2631, h2632, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2634 | h2634
                            · linarith only [h0, h2548, h2553, h2631, h2634, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases h0bigk with h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c | h2636c
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [hlam, p2636_0]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h0, hlam, p2636_0]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h1647, hlam, p2636_0]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h2158, hlam, p2636_0]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h2377, hlam, p2636_0]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2636_1, u2elo1]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [hlam, p2636_0]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2636_1, u2elo1]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h0, h2158, hc01, hlam, hphi, ht12, p2636_1, u2elo1]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h0, h2158, h2553, hc01, hlam, hphi, ht12, p2636_1, u2elo1]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h1647, h2627, hc01, hlam, hphi, ht12, p2636_1, u2elo1]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h2548, hlam, p2636_0]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [hlam, p2636_0]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h1647, h2158, h2627, hc01, hlam, hphi, ht12, p2636_1, u2elo1]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h1647, h2158, h2553, h2627, hc01, hlam, hphi, ht12, p2636_1, u2elo1]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h2553, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2636_1]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h2549, hlam, p2636_0]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h2551, hlam, p2636_1]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [hlam, p2636_0]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h2553, hlam, p2636_1]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h2377, h2627, h2630, hc01, hlam, hphi, ht12, p2636_1, u2elo1]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h2550, hlam, p2636_0]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h2552, hlam, p2636_0]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [h2377, h2627, h2630, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2636_1, u2elo1]
                              · have p2636_0 := h2636c.1
                                have p2636_1 := h2636c.2.1
                                have p2636_2 := h2636c.2.2.1
                                have p2636_3 := h2636c.2.2.2
                                linarith only [hlam, p2636_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2662 | h2662
                          · linarith only [h2551, h2553, h2631, h2662, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2664 | h2664
                            · linarith only [h1647, h2377, h2551, h2553, h2627, h2664, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases h0bigk with h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c | h2666c
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [hlam, p2666_0]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h0, hlam, p2666_0]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h1647, hlam, p2666_0]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h2158, hlam, p2666_0]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h2377, hlam, p2666_0]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2666_1, u2elo1]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [hlam, p2666_0]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2666_1, u2elo1]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h0, h2551, h2631, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2666_1, u2elo1]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h0, h2551, h2553, h2631, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2666_1, u2elo1]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h1647, h2627, hc01, hlam, hphi, ht12, p2666_1, u2elo1]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h2548, hlam, p2666_0]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [hlam, p2666_0]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h1647, h2551, h2627, h2631, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2666_1, u2elo1]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h1647, h2551, h2553, h2627, h2631, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2666_1, u2elo1]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h2158, hc01, hc14, hlam, hphi, p2666_1]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h2549, hlam, p2666_0]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h2551, hlam, p2666_1]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [hlam, p2666_0]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h2553, hlam, p2666_1]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h2377, h2627, h2630, hc01, hlam, hphi, ht12, p2666_1, u2elo1]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h2550, hlam, p2666_0]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h2552, hlam, p2666_0]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [h2377, h2627, h2630, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2666_1, u2elo1]
                              · have p2666_0 := h2666c.1
                                have p2666_1 := h2666c.2.1
                                have p2666_2 := h2666c.2.2.1
                                have p2666_3 := h2666c.2.2.2
                                linarith only [hlam, p2666_0]
                      · linarith only [h1647, h2552, h2630, hlam]
                    · linarith only [h0, h2550, h2629, hlam]
                  · linarith only [h0, h2628, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2627, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2696 | h2696
              · linarith only [h2551, h2552, h2696, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2698 | h2698
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2699 | h2699
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2700 | h2700
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2701 | h2701
                      · linarith only [h2551, h2552, h2698, h2701, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2703 | h2703
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2704 | h2704
                          · linarith only [h2549, h2696, h2704, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2706 | h2706
                            · linarith only [h2696, h2703, h2706, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · rcases h0bigk with h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c | h2708c
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
                                linarith only [h1647, hlam, p2708_0]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h2158, hlam, p2708_0]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h2377, hlam, p2708_0]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p2708_1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [hlam, p2708_0]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2708_1, u2elo1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h0, h2158, hc01, hlam, hphi, ht12, p2708_1, u2elo1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h0, h2548, h2552, h2703, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2708_1, u2elo1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h1647, h2701, h2706, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2708_1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h2548, hlam, p2708_0]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [hlam, p2708_0]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h1647, h2158, h2701, h2706, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2708_1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h2552, hlam, p2708_1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h2158, hc01, hc14, hlam, hphi, p2708_1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h2549, hlam, p2708_0]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h2551, hlam, p2708_1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [hlam, p2708_0]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h2696, hlam, p2708_1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h2377, hc01, hc15, hlam, hphi, p2708_1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h2550, hlam, p2708_0]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h0, h2550, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2708_1, u2elo1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [h0, h2158, h2550, hc01, hlam, hphi, ht12, p2708_1, u2elo1]
                              · have p2708_0 := h2708c.1
                                have p2708_1 := h2708c.2.1
                                have p2708_2 := h2708c.2.2.1
                                have p2708_3 := h2708c.2.2.2
                                linarith only [hlam, p2708_0]
                        · linarith only [h1647, h2551, h2701, h2703, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h2700, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1647, h2698, h2699, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2698, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2738 | h2738
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2739 | h2739
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2740 | h2740
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2741 | h2741
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2742 | h2742
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2743 | h2743
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2744 | h2744
                        · linarith only [h2548, h2551, h2738, h2744, hc02, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2746 | h2746
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2747 | h2747
                            · rcases h0bigk with h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c | h2748c
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h0, hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h1647, hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h2158, hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h2377, hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p2748_1]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h0, h2738, h2747, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2748_1, u2elo1]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h0, h2551, h2738, h2747, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2748_1, u2elo1]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2748_1, u2elo1]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h2551, hc01, hc34, hlam, hphi, ht12, ht23, p2748_1]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h2548, hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h2551, hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h0, h2377, h2549, h2551, hc01, hlam, hphi, ht12, p2748_1, u2elo1]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h0, h2549, hc01, hlam, hphi, ht12, p2748_1, u2elo1]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h2549, hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h0, h2549, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2748_1, u2elo1]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h0, h2377, h2549, hc01, hlam, hphi, ht12, p2748_1, u2elo1]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h2377, hc01, hc15, hlam, hphi, p2748_1]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h2550, hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h2738, hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [h2739, hlam, p2748_0]
                              · have p2748_0 := h2748c.1
                                have p2748_1 := h2748c.2.1
                                have p2748_2 := h2748c.2.2.1
                                have p2748_3 := h2748c.2.2.2
                                linarith only [hlam, p2748_0]
                            · linarith only [h0, h2549, h2746, h2747, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2775 | h2775
                            · linarith only [h2551, h2738, h2744, h2746, h2775, hc23, hc34, hlam, hphi]
                            · linarith only [h2551, h2739, h2775, hlam]
                      · linarith only [h1647, h2551, h2738, h2743, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h2742, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1647, h2740, h2741, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2740, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2551, h2738, h2739, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2783 | h2783
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2784 | h2784
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2785 | h2785
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2786 | h2786
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2787 | h2787
                      · linarith only [h1647, h2738, h2784, h2787, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2789 | h2789
                        · linarith only [h0, h2548, h2551, h2783, h2789, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2791 | h2791
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2792 | h2792
                            · rcases h0bigk with h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c | h2793c
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h0, hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h1647, hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h2158, hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h2377, hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2793_1, u2elo1]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h0, h1647, hc01, hlam, hphi, ht12, p2793_1, u2elo1]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h0, h1647, h2738, h2783, hc01, hlam, hphi, ht12, p2793_1, u2elo1]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h0, h1647, h2738, hc01, hlam, hphi, ht12, p2793_1, u2elo1]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h1647, h2786, h2787, hc01, hlam, hphi, ht12, p2793_1, u2elo1]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h2548, hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h2551, hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h2738, hlam, p2793_1]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h2158, hc01, hc14, hlam, hphi, p2793_1]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h2549, hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h0, h2549, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2793_1, u2elo1]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h0, h1647, h2549, h2738, hc01, hlam, hphi, ht12, p2793_1, u2elo1]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h2377, h2786, hc01, hlam, hphi, ht12, p2793_1, u2elo1]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h2550, hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h1647, h2377, h2786, hc01, hlam, hphi, ht12, p2793_1, u2elo1]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [h2783, hlam, p2793_0]
                              · have p2793_0 := h2793c.1
                                have p2793_1 := h2793c.2.1
                                have p2793_2 := h2793c.2.2.1
                                have p2793_3 := h2793c.2.2.2
                                linarith only [hlam, p2793_0]
                            · linarith only [h0, h2549, h2791, h2792, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2820 | h2820
                            · rcases h0bigk with h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c | h2821c
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h0, hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h1647, hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h2158, hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h2377, hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2821_1, u2elo1]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h0, h1647, hc01, hlam, hphi, ht12, p2821_1, u2elo1]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2821_1, u2elo1]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2821_1, u2elo1]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h1647, hc01, hc13, hlam, hphi, p2821_1]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h2548, hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h2551, hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h2738, hlam, p2821_1]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h2158, h2785, hc01, hlam, hphi, ht12, p2821_1, u2elo1]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h2549, hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h2158, h2785, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2821_1, u2elo1]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h1647, h2158, h2738, h2785, hc01, hlam, hphi, ht12, p2821_1, u2elo1]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h2377, h2786, hc01, hlam, hphi, ht12, p2821_1, u2elo1]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h2550, hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h1647, h2377, h2786, hc01, hlam, hphi, ht12, p2821_1, u2elo1]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [h2783, hlam, p2821_0]
                              · have p2821_0 := h2821c.1
                                have p2821_1 := h2821c.2.1
                                have p2821_2 := h2821c.2.2.1
                                have p2821_3 := h2821c.2.2.2
                                linarith only [hlam, p2821_0]
                            · linarith only [h2551, h2783, h2820, hlam]
                    · linarith only [h0, h2550, h2786, hlam]
                  · linarith only [h0, h2785, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2784, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2851 | h2851
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2852 | h2852
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2853 | h2853
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2854 | h2854
                      · linarith only [h1647, h2738, h2851, h2854, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2856 | h2856
                        · linarith only [h0, h2158, h2548, h2551, h2856, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2858 | h2858
                          · linarith only [h0, h2549, h2551, h2783, h2858, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2860 | h2860
                            · rcases h0bigk with h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c | h2861c
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h0, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h1647, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2158, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2377, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2861_1, u2elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h0, h1647, hc01, hlam, hphi, ht12, p2861_1, u2elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h0, h1647, h2551, hc01, hlam, hphi, ht12, p2861_1, u2elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2861_1, u2elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h1647, h2853, h2854, hc01, hlam, hphi, ht12, p2861_1, u2elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2548, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2551, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2738, hlam, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2158, h2852, hc01, hlam, hphi, ht12, p2861_1, u2elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2549, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2551, hc03, hc34, hlam, hphi, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2783, hlam, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2783, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2861_1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2550, hlam, p2861_0]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h1647, h2377, h2853, hc01, hlam, hphi, ht12, p2861_1, u2elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [h2377, h2853, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2861_1, u2elo1]
                              · have p2861_0 := h2861c.1
                                have p2861_1 := h2861c.2.1
                                have p2861_2 := h2861c.2.2.1
                                have p2861_3 := h2861c.2.2.2
                                linarith only [hlam, p2861_0]
                            · rcases h0bigk with h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c | h2887c
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [hlam, p2887_0]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h0, hlam, p2887_0]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h1647, hlam, p2887_0]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h2158, hlam, p2887_0]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h2377, hlam, p2887_0]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2887_1, u2elo1]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [hlam, p2887_0]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h0, h1647, hc01, hlam, hphi, ht12, p2887_1, u2elo1]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h0, h1647, h2551, hc01, hlam, hphi, ht12, p2887_1, u2elo1]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2887_1, u2elo1]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h1647, h2854, h2860, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2887_1]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h2548, hlam, p2887_0]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [hlam, p2887_0]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h2551, hlam, p2887_0]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h2738, hlam, p2887_1]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h2158, h2852, hc01, hlam, hphi, ht12, p2887_1, u2elo1]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h2549, hlam, p2887_0]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h2551, h2860, hc03, hc45, hlam, hphi, ht34, p2887_1]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [hlam, p2887_0]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h2783, hlam, p2887_1]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h2377, h2853, hc01, hlam, hphi, ht12, p2887_1, u2elo1]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h2550, hlam, p2887_0]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h1647, h2377, h2853, hc01, hlam, hphi, ht12, p2887_1, u2elo1]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [h2377, h2853, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2887_1, u2elo1]
                              · have p2887_0 := h2887c.1
                                have p2887_1 := h2887c.2.1
                                have p2887_2 := h2887c.2.2.1
                                have p2887_3 := h2887c.2.2.2
                                linarith only [hlam, p2887_0]
                    · linarith only [h0, h2550, h2853, hlam]
                  · linarith only [h0, h2852, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2851, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2916 | h2916
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2917 | h2917
            · linarith only [h2548, h2550, h2917, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2919 | h2919
              · linarith only [h2549, h2550, h2919, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2921 | h2921
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2922 | h2922
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2923 | h2923
                    · linarith only [h2550, h2923, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h2923, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1647, h2921, h2922, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h2548, h2550, h2921, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2928 | h2928
            · linarith only [h2549, h2550, h2916, h2928, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2930 | h2930
              · linarith only [h2549, h2550, h2930, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2932 | h2932
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2933 | h2933
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2934 | h2934
                    · linarith only [h2550, h2934, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h2934, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1647, h2932, h2933, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2932, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2939 | h2939
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2940 | h2940
          · linarith only [h2548, h2549, h2940, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2942 | h2942
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2943 | h2943
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2944 | h2944
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2945 | h2945
                  · linarith only [h2549, h2945, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2945, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2944, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2548, h2549, h2942, h2943, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2950 | h2950
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2951 | h2951
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2952 | h2952
                  · linarith only [h2549, h2952, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2952, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2951, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2549, h2939, h2950, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2957 | h2957
          · linarith only [h2548, h2549, h2957, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2959 | h2959
            · linarith only [h2548, h2939, h2959, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2961 | h2961
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2962 | h2962
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2963 | h2963
                  · linarith only [h2549, h2963, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2963, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2962, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2967 | h2967
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2968 | h2968
                  · linarith only [h2549, h2968, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2968, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2967, hc01, hlam, hphi, ht12, u2elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2972 | h2972
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2973 | h2973
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2974 | h2974
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2975 | h2975
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2976 | h2976
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2977 | h2977
                · linarith only [h2548, h2977, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h2977, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2980 | h2980
                · linarith only [h2548, h2972, h2980, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h2980, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h2548, h2973, h2975, hlam]
          · linarith only [h2548, h2972, h2974, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2985 | h2985
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2986 | h2986
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2987 | h2987
              · linarith only [h2972, h2973, h2987, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2989 | h2989
                · linarith only [h2548, h2972, h2989, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h2989, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2992 | h2992
              · linarith only [h2548, h2972, h2986, h2992, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2994 | h2994
                · linarith only [h2548, h2972, h2994, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h2994, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h2548, h2972, h2985, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2998 | h2998
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2999 | h2999
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3000 | h3000
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3001 | h3001
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3002 | h3002
                · linarith only [h2548, h3002, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h3002, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2972, h2998, h3001, hlam]
            · linarith only [h2972, h2998, h2999, h3000, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3007 | h3007
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3008 | h3008
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3009 | h3009
                · linarith only [h2548, h2998, h3009, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h3009, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2548, h2998, h2999, h3008, hlam]
            · linarith only [h2548, h2998, h3007, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3014 | h3014
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3015 | h3015
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3016 | h3016
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3017 | h3017
                · linarith only [h0, h2548, h3017, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h3017, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3020 | h3020
                · linarith only [h0, h2548, h3020, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h3020, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3023 | h3023
              · linarith only [h3014, h3015, h3023, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3025 | h3025
                · linarith only [h0, h2548, h3025, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h3025, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3028 | h3028
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3029 | h3029
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3030 | h3030
                · linarith only [h0, h2548, h3030, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h3030, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h3014, h3028, h3029, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3034 | h3034
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3035 | h3035
                · linarith only [h0, h2548, h3035, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h3035, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3038 | h3038
                · linarith only [h0, h2548, h3038, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h3038, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1647 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2158 | h2158
  · exact r1l7_20_12_H_I_L_0_x1_x1_x0 m hb0 hb2 h0 h1647 h2158
  · exact r1l7_20_12_H_I_L_0_x1_x1_x1 m hb0 hb2 h0 h1647 h2158

set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1647 | h1647
  · exact r1l7_20_12_H_I_L_0_x1_x0 m hb0 hb2 h0 h1647
  · exact r1l7_20_12_H_I_L_0_x1_x1 m hb0 hb2 h0 h1647

set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_H_I_L_0_x0 m hb0 hb2 h0
  · exact r1l7_20_12_H_I_L_0_x1 m hb0 hb2 h0

end R2N4
