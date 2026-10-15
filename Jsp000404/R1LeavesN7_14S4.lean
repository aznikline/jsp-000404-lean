import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_14S1
import Jsp000404.R1LeavesN7_14S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1025 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1371 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1499 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h2443 | h2443
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2444 | h2444
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2445 | h2445
      · linarith only [h0, h2443, h2445, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2447 | h2447
        · linarith only [h0, h1025, h2447, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2449 | h2449
          · linarith only [h0, h1371, h2449, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2451 | h2451
            · linarith only [h1, h1499, h2451, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2453 | h2453
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2454 | h2454
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2455 | h2455
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2456 | h2456
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2457 | h2457
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2458 | h2458
                        · rcases h0bigk with h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c | h2459c
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [hlam, p2459_0]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            rcases p2459_3 (m.d 0 1) (by simp) with h2461 | h2461
                            · rcases p2459_3 (m.d 0 2) (by simp) with h2462 | h2462
                              · linarith only [h0, h2462, hlam]
                              · rcases p2459_3 (m.d 0 3) (by simp) with h2464 | h2464
                                · linarith only [h1, h2464, hlam]
                                · linarith only [h2464, h4, hlam]
                            · linarith only [h0, h2461, hlam]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h2443, h2458, hc45, hlam, hphi, ht0b, ht5b, p2459_1, u0elo0]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h1499, h2443, h2458, hc45, hlam, hphi, ht0b, ht5b, p2459_1, u0elo0]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            rcases p2459_3 (m.d 0 1) (by simp) with h2470 | h2470
                            · rcases p2459_3 (m.d 0 2) (by simp) with h2471 | h2471
                              · linarith only [h0, h2471, hlam]
                              · rcases p2459_3 (m.d 0 3) (by simp) with h2473 | h2473
                                · linarith only [h1, h2473, hlam]
                                · linarith only [h2443, h2473, hlam]
                            · linarith only [h2470, h3, hlam]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h0, hlam, p2459_0]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [hlam, p2459_0]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h4, hlam, p2459_0]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h1025, hlam, p2459_1]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h1371, hlam, p2459_0]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h1, hlam, p2459_1]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h0, h1499, h2455, hc12, hc23, hlam, hphi, p2459_1]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [hlam, p2459_0]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h1499, hlam, p2459_1]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h1499, h2455, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2459_1]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h2, hlam, p2459_0]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h0, h1499, h2455, hc12, hc23, hlam, hphi, p2459_1]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h1, h1499, h2453, h2455, h2458, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2459_1]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [hlam, p2459_0]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h0, h1371, h1499, h2455, hc12, hc23, hlam, hphi, p2459_1]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h3, hlam, p2459_0]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h0, h1499, h2443, h2455, hc12, hc23, hlam, hphi, p2459_1]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h2443, hlam, p2459_0]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [h2444, hlam, p2459_1]
                          · have p2459_0 := h2459c.1
                            have p2459_1 := h2459c.2.1
                            have p2459_2 := h2459c.2.2.1
                            have p2459_3 := h2459c.2.2.2
                            linarith only [hlam, p2459_0]
                        · linarith only [h1499, h2, h2444, h2458, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h1499, h2, h2454, h2455, h2457, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h1, h1499, h2453, h2456, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2500 | h2500
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2501 | h2501
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2502 | h2502
                        · rcases h0bigk with h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c | h2503c
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            rcases p2503_3 (m.d 0 1) (by simp) with h2505 | h2505
                            · rcases p2503_3 (m.d 0 2) (by simp) with h2506 | h2506
                              · linarith only [h0, h2506, hlam]
                              · rcases p2503_3 (m.d 0 3) (by simp) with h2508 | h2508
                                · linarith only [h1, h2508, hlam]
                                · linarith only [h2508, h4, hlam]
                            · linarith only [h0, h2505, hlam]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2443, hc35, hlam, hphi, ht0b, ht5b, p2503_1, u0elo0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h1499, h2443, hc35, hlam, hphi, ht0b, ht5b, p2503_1, u0elo0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            rcases p2503_3 (m.d 0 1) (by simp) with h2514 | h2514
                            · rcases p2503_3 (m.d 0 2) (by simp) with h2515 | h2515
                              · linarith only [h0, h2515, hlam]
                              · rcases p2503_3 (m.d 0 3) (by simp) with h2517 | h2517
                                · linarith only [h1, h2517, hlam]
                                · linarith only [h2443, h2517, hlam]
                            · linarith only [h2514, h3, hlam]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h0, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h4, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h1025, hlam, p2503_1]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h1371, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h1, hlam, p2503_1]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h0, h2455, h4, hc12, hc34, hlam, hphi, ht23, p2503_1]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h1499, hlam, p2503_1]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2449, h2455, h3, h4, hc12, hc34, hlam, hphi, ht23, p2503_1]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            rcases p2503_3 (m.d 0 1) (by simp) with h2532 | h2532
                            · rcases p2503_3 (m.d 0 2) (by simp) with h2533 | h2533
                              · linarith only [h1025, h2533, hlam]
                              · rcases p2503_3 (m.d 0 3) (by simp) with h2535 | h2535
                                · linarith only [h1499, h2535, hlam]
                                · linarith only [h2535, h4, hlam]
                            · linarith only [h0, h2532, hlam]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h1, h2453, h2502, hc45, hlam, hphi, ht0b, ht5b, p2503_1, u0elo3]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            rcases p2503_3 (m.d 0 1) (by simp) with h2541 | h2541
                            · rcases p2503_3 (m.d 0 2) (by simp) with h2542 | h2542
                              · linarith only [h1025, h2542, hlam]
                              · rcases p2503_3 (m.d 0 3) (by simp) with h2544 | h2544
                                · linarith only [h1499, h2544, hlam]
                                · linarith only [h2443, h2544, hlam]
                            · linarith only [h2541, h3, hlam]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h3, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h0, h2443, h2455, h4, hc12, hc34, hlam, hphi, ht23, p2503_1]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2443, hlam, p2503_0]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [h2444, hlam, p2503_1]
                          · have p2503_0 := h2503c.1
                            have p2503_1 := h2503c.2.1
                            have p2503_2 := h2503c.2.2.1
                            have p2503_3 := h2503c.2.2.2
                            linarith only [hlam, p2503_0]
                        · linarith only [h0, h2455, h2502, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h1025, h2444, h2501, hlam]
                    · linarith only [h0, h1, h2453, h2500, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h2444, h2451, h2453, h2454, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
              · linarith only [h1499, h2443, h2453, hc13, hc34, hlam, hphi]
    · linarith only [h1499, h2443, h2444, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2559 | h2559
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2560 | h2560
      · linarith only [h0, h2560, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2562 | h2562
        · linarith only [h0, h1025, h2559, h2562, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2564 | h2564
          · linarith only [h0, h1371, h2564, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2566 | h2566
            · linarith only [h1, h1499, h2566, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2568 | h2568
              · linarith only [h1, h2443, h2568, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2570 | h2570
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2571 | h2571
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2572 | h2572
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2573 | h2573
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2574 | h2574
                        · rcases h0bigk with h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [hlam, p2575_0]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            rcases p2575_3 (m.d 0 1) (by simp) with h2577 | h2577
                            · rcases p2575_3 (m.d 0 2) (by simp) with h2578 | h2578
                              · linarith only [h0, h2578, hlam]
                              · rcases p2575_3 (m.d 0 3) (by simp) with h2580 | h2580
                                · linarith only [h1, h2580, hlam]
                                · linarith only [h2580, h4, hlam]
                            · linarith only [h0, h2577, hlam]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            rcases p2575_3 (m.d 0 1) (by simp) with h2584 | h2584
                            · rcases p2575_3 (m.d 0 2) (by simp) with h2585 | h2585
                              · linarith only [h0, h2585, hlam]
                              · rcases p2575_3 (m.d 0 3) (by simp) with h2587 | h2587
                                · linarith only [h1, h2587, hlam]
                                · rcases p2575_3 (m.d 0 4) (by simp) with h2589 | h2589
                                  · linarith only [h2, h2589, hlam]
                                  · linarith only [h1499, h2589, hlam]
                            · linarith only [h1, h2584, hlam]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h2, h2570, hc45, hlam, hphi, ht0b, ht5b, p2575_1, u0elo0]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            rcases p2575_3 (m.d 0 1) (by simp) with h2594 | h2594
                            · rcases p2575_3 (m.d 0 2) (by simp) with h2595 | h2595
                              · linarith only [h0, h2595, hlam]
                              · rcases p2575_3 (m.d 0 3) (by simp) with h2597 | h2597
                                · linarith only [h1, h2597, hlam]
                                · rcases p2575_3 (m.d 0 4) (by simp) with h2599 | h2599
                                  · linarith only [h2, h2599, hlam]
                                  · linarith only [h2559, h2599, hlam]
                            · linarith only [h2594, h3, hlam]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h0, hlam, p2575_0]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [hlam, p2575_0]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h4, hlam, p2575_0]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h1025, hlam, p2575_1]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h1371, hlam, p2575_0]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h1, hlam, p2575_1]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h0, h2443, h2571, h2574, hc12, hc23, hlam, hphi, p2575_1]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [hlam, p2575_0]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h1499, hlam, p2575_1]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h2443, hlam, p2575_1]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h2, hlam, p2575_0]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h0, h1499, h2571, hc12, hc23, hlam, hphi, p2575_1]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h0, h1499, h2571, h4, hc12, hc23, hlam, hphi, p2575_1]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [hlam, p2575_0]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h0, h1499, h2443, h2571, h4, hc12, hc23, hlam, hphi, p2575_1]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h3, hlam, p2575_0]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h0, h2443, h2571, h2574, hc12, hc23, hlam, hphi, p2575_1]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h0, h2443, h2571, h2574, h4, hc12, hc23, hlam, hphi, p2575_1]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [h2559, hlam, p2575_1]
                          · have p2575_0 := h2575c.1
                            have p2575_1 := h2575c.2.1
                            have p2575_2 := h2575c.2.2.1
                            have p2575_3 := h2575c.2.2.2
                            linarith only [hlam, p2575_0]
                        · linarith only [h1499, h2, h2570, h2574, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1499, h2, h2570, h2571, h2573, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h1499, h2571, h2572, h4, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2626 | h2626
                    · linarith only [h0, h2443, h2571, h2626, h4, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2628 | h2628
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2629 | h2629
                        · rcases h0bigk with h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c | h2630c
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [hlam, p2630_0]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            rcases p2630_3 (m.d 0 1) (by simp) with h2632 | h2632
                            · rcases p2630_3 (m.d 0 2) (by simp) with h2633 | h2633
                              · linarith only [h0, h2633, hlam]
                              · rcases p2630_3 (m.d 0 3) (by simp) with h2635 | h2635
                                · linarith only [h1, h2635, hlam]
                                · linarith only [h2635, h4, hlam]
                            · linarith only [h0, h2632, hlam]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            rcases p2630_3 (m.d 0 1) (by simp) with h2639 | h2639
                            · rcases p2630_3 (m.d 0 2) (by simp) with h2640 | h2640
                              · linarith only [h0, h2640, hlam]
                              · rcases p2630_3 (m.d 0 3) (by simp) with h2642 | h2642
                                · linarith only [h1, h2642, hlam]
                                · rcases p2630_3 (m.d 0 4) (by simp) with h2644 | h2644
                                  · linarith only [h2, h2644, hlam]
                                  · linarith only [h1499, h2644, hlam]
                            · linarith only [h1, h2639, hlam]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [h2, h2570, hc45, hlam, hphi, ht0b, ht5b, p2630_1, u0elo0]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            rcases p2630_3 (m.d 0 1) (by simp) with h2649 | h2649
                            · rcases p2630_3 (m.d 0 2) (by simp) with h2650 | h2650
                              · linarith only [h0, h2650, hlam]
                              · rcases p2630_3 (m.d 0 3) (by simp) with h2652 | h2652
                                · linarith only [h1, h2652, hlam]
                                · rcases p2630_3 (m.d 0 4) (by simp) with h2654 | h2654
                                  · linarith only [h2, h2654, hlam]
                                  · linarith only [h2559, h2654, hlam]
                            · linarith only [h2649, h3, hlam]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [h0, hlam, p2630_0]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [hlam, p2630_0]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [h4, hlam, p2630_0]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [h1025, hlam, p2630_1]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [h1371, hlam, p2630_0]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [h1, hlam, p2630_1]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [h0, h2626, h2629, h4, hc12, hc34, hlam, hphi, ht23, p2630_1]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [hlam, p2630_0]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [h1499, hlam, p2630_1]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [h2443, hlam, p2630_1]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [h2, hlam, p2630_0]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            rcases p2630_3 (m.d 0 1) (by simp) with h2669 | h2669
                            · rcases p2630_3 (m.d 0 2) (by simp) with h2670 | h2670
                              · linarith only [h1025, h2670, hlam]
                              · rcases p2630_3 (m.d 0 3) (by simp) with h2672 | h2672
                                · linarith only [h1499, h2672, hlam]
                                · linarith only [h2672, h4, hlam]
                            · linarith only [h0, h2669, hlam]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            rcases p2630_3 (m.d 0 1) (by simp) with h2676 | h2676
                            · rcases p2630_3 (m.d 0 2) (by simp) with h2677 | h2677
                              · linarith only [h1025, h2677, hlam]
                              · rcases p2630_3 (m.d 0 3) (by simp) with h2679 | h2679
                                · linarith only [h1499, h2679, hlam]
                                · rcases p2630_3 (m.d 0 4) (by simp) with h2681 | h2681
                                  · rcases p2630_3 (m.d 0 5) (by simp) with h2682 | h2682
                                    · linarith only [h2559, h2682, hlam]
                                    · linarith only [h2443, h2682, hlam]
                                  · linarith only [h1499, h2681, hlam]
                            · linarith only [h1, h2676, hlam]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [hlam, p2630_0]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            rcases p2630_3 (m.d 0 1) (by simp) with h2688 | h2688
                            · rcases p2630_3 (m.d 0 2) (by simp) with h2689 | h2689
                              · linarith only [h1025, h2689, hlam]
                              · rcases p2630_3 (m.d 0 3) (by simp) with h2691 | h2691
                                · linarith only [h1499, h2691, hlam]
                                · rcases p2630_3 (m.d 0 4) (by simp) with h2693 | h2693
                                  · rcases p2630_3 (m.d 0 5) (by simp) with h2694 | h2694
                                    · linarith only [h2559, h2694, hlam]
                                    · rcases h2bigk with h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c | h2696c
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h2443, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2630_1, p2696_1, u0elo3]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h4, hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h1025, hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h1371, hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h0, hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h2560, hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h2562, hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h2564, hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h2626, h2629, hc02, hc34, hlam, hphi, ht23, p2696_1]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h2626, h2629, hc12, hc34, hlam, hphi, ht23, p2696_1]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h2571, hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h2626, hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        rcases p2696_3 (m.d 0 2) (by simp) with h2712 | h2712
                                        · linarith only [h2712, hlam, p2696_0]
                                        · rcases p2696_3 (m.d 1 2) (by simp) with h2714 | h2714
                                          · linarith only [h2562, h2714, hlam]
                                          · rcases p2696_3 (m.d 2 3) (by simp) with h2716 | h2716
                                            · linarith only [h2571, h2716, hlam]
                                            · linarith only [h2716, h4, hlam]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        rcases p2696_3 (m.d 0 2) (by simp) with h2719 | h2719
                                        · linarith only [h1025, h2719, hlam]
                                        · linarith only [h0, h2719, hlam]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h0, h4, hc12, hc24, hlam, hphi, p2696_1]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h0, h2571, h2626, h4, hc12, hc34, hlam, hphi, ht23, p2696_1]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        rcases p2696_3 (m.d 0 2) (by simp) with h2725 | h2725
                                        · linarith only [h2725, hlam, p2696_0]
                                        · rcases p2696_3 (m.d 1 2) (by simp) with h2727 | h2727
                                          · linarith only [h2564, h2727, hlam]
                                          · rcases p2696_3 (m.d 2 3) (by simp) with h2729 | h2729
                                            · linarith only [h2626, h2729, hlam]
                                            · linarith only [h2729, h4, hlam]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        rcases p2696_3 (m.d 0 2) (by simp) with h2732 | h2732
                                        · linarith only [h1371, h2732, hlam]
                                        · linarith only [h0, h2732, hlam]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p2696_1]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [h2628, hlam, p2696_0]
                                      · have p2696_0 := h2696c.1
                                        have p2696_1 := h2696c.2.1
                                        have p2696_2 := h2696c.2.2.1
                                        have p2696_3 := h2696c.2.2.2
                                        linarith only [hlam, p2696_0]
                                  · linarith only [h2559, h2693, hlam]
                            · linarith only [h2688, h3, hlam]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [h3, hlam, p2630_0]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            rcases p2630_3 (m.d 0 1) (by simp) with h2741 | h2741
                            · rcases p2630_3 (m.d 0 2) (by simp) with h2742 | h2742
                              · linarith only [h1371, h2742, hlam]
                              · rcases p2630_3 (m.d 0 3) (by simp) with h2744 | h2744
                                · linarith only [h2443, h2744, hlam]
                                · linarith only [h2744, h4, hlam]
                            · linarith only [h0, h2741, hlam]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            rcases p2630_3 (m.d 0 1) (by simp) with h2748 | h2748
                            · rcases p2630_3 (m.d 0 2) (by simp) with h2749 | h2749
                              · linarith only [h1371, h2749, hlam]
                              · rcases p2630_3 (m.d 0 3) (by simp) with h2751 | h2751
                                · linarith only [h2443, h2751, hlam]
                                · rcases p2630_3 (m.d 0 4) (by simp) with h2753 | h2753
                                  · rcases p2630_3 (m.d 0 5) (by simp) with h2754 | h2754
                                    · rcases h2bigk with h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c | h2755c
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h4, hc12, hc23, hlam, hphi, p2755_1]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h4, hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h1025, hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h1371, hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h0, hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h2560, hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h2562, hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h2564, hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h2571, hc02, hc34, hlam, hphi, ht23, p2755_1]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h2571, hc12, hc34, hlam, hphi, ht23, p2755_1]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h2571, hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h2626, hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        rcases p2755_3 (m.d 0 2) (by simp) with h2771 | h2771
                                        · linarith only [h2771, hlam, p2755_0]
                                        · rcases p2755_3 (m.d 1 2) (by simp) with h2773 | h2773
                                          · linarith only [h2562, h2773, hlam]
                                          · rcases p2755_3 (m.d 2 3) (by simp) with h2775 | h2775
                                            · linarith only [h2571, h2775, hlam]
                                            · linarith only [h2775, h4, hlam]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        rcases p2755_3 (m.d 0 2) (by simp) with h2778 | h2778
                                        · linarith only [h1025, h2778, hlam]
                                        · linarith only [h0, h2778, hlam]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h0, h2571, h4, hc12, hc34, hlam, hphi, ht23, p2755_1]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h0, h1371, h2571, hc12, hc34, hlam, hphi, ht23, p2755_1]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        rcases p2755_3 (m.d 0 2) (by simp) with h2784 | h2784
                                        · linarith only [h2784, hlam, p2755_0]
                                        · rcases p2755_3 (m.d 1 2) (by simp) with h2786 | h2786
                                          · linarith only [h2564, h2786, hlam]
                                          · rcases p2755_3 (m.d 2 3) (by simp) with h2788 | h2788
                                            · linarith only [h2626, h2788, hlam]
                                            · linarith only [h2788, h4, hlam]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        rcases p2755_3 (m.d 0 2) (by simp) with h2791 | h2791
                                        · linarith only [h1371, h2791, hlam]
                                        · linarith only [h0, h2791, hlam]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p2755_1]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [h2628, hlam, p2755_0]
                                      · have p2755_0 := h2755c.1
                                        have p2755_1 := h2755c.2.1
                                        have p2755_2 := h2755c.2.2.1
                                        have p2755_3 := h2755c.2.2.2
                                        linarith only [hlam, p2755_0]
                                    · linarith only [h2443, h2754, hlam]
                                  · linarith only [h1499, h2753, hlam]
                            · linarith only [h1, h2748, hlam]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [h2559, hlam, p2630_1]
                          · have p2630_0 := h2630c.1
                            have p2630_1 := h2630c.2.1
                            have p2630_2 := h2630c.2.2.1
                            have p2630_3 := h2630c.2.2.2
                            linarith only [hlam, p2630_0]
                        · linarith only [h1025, h2559, h2571, h2629, hlam]
                      · linarith only [h1025, h2, h2570, h2628, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2804 | h2804
                  · linarith only [h1499, h2559, h2560, h2566, h2570, h2804, hc12, hc23, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2806 | h2806
                    · linarith only [h0, h2443, h2804, h2806, h4, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2808 | h2808
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2809 | h2809
                        · rcases h0bigk with h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c | h2810c
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [hlam, p2810_0]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            rcases p2810_3 (m.d 0 1) (by simp) with h2812 | h2812
                            · rcases p2810_3 (m.d 0 2) (by simp) with h2813 | h2813
                              · linarith only [h0, h2813, hlam]
                              · rcases p2810_3 (m.d 0 3) (by simp) with h2815 | h2815
                                · linarith only [h1, h2815, hlam]
                                · linarith only [h2815, h4, hlam]
                            · linarith only [h0, h2812, hlam]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            rcases p2810_3 (m.d 0 1) (by simp) with h2819 | h2819
                            · rcases p2810_3 (m.d 0 2) (by simp) with h2820 | h2820
                              · linarith only [h0, h2820, hlam]
                              · rcases p2810_3 (m.d 0 3) (by simp) with h2822 | h2822
                                · linarith only [h1, h2822, hlam]
                                · rcases p2810_3 (m.d 0 4) (by simp) with h2824 | h2824
                                  · linarith only [h2, h2824, hlam]
                                  · linarith only [h1499, h2824, hlam]
                            · linarith only [h1, h2819, hlam]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h2559, h2560, h2566, h2570, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2810_1, u0elo0]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h2559, h2560, h2566, h2570, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2810_1, u0elo0]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h0, hlam, p2810_0]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [hlam, p2810_0]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h4, hlam, p2810_0]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h1025, hlam, p2810_1]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h1371, hlam, p2810_0]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h1, hlam, p2810_1]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h0, h2806, h2809, h4, hc12, hc34, hlam, hphi, ht23, p2810_1]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [hlam, p2810_0]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h1499, hlam, p2810_1]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h2443, hlam, p2810_1]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h2, hlam, p2810_0]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            rcases p2810_3 (m.d 0 1) (by simp) with h2841 | h2841
                            · rcases p2810_3 (m.d 0 2) (by simp) with h2842 | h2842
                              · linarith only [h1025, h2842, hlam]
                              · rcases p2810_3 (m.d 0 3) (by simp) with h2844 | h2844
                                · linarith only [h1499, h2844, hlam]
                                · linarith only [h2844, h4, hlam]
                            · linarith only [h0, h2841, hlam]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            rcases p2810_3 (m.d 0 1) (by simp) with h2848 | h2848
                            · rcases p2810_3 (m.d 0 2) (by simp) with h2849 | h2849
                              · linarith only [h1025, h2849, hlam]
                              · rcases p2810_3 (m.d 0 3) (by simp) with h2851 | h2851
                                · linarith only [h1499, h2851, hlam]
                                · rcases p2810_3 (m.d 0 4) (by simp) with h2853 | h2853
                                  · rcases p2810_3 (m.d 0 5) (by simp) with h2854 | h2854
                                    · linarith only [h2559, h2854, hlam]
                                    · linarith only [h2443, h2854, hlam]
                                  · linarith only [h1499, h2853, hlam]
                            · linarith only [h1, h2848, hlam]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [hlam, p2810_0]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h2559, h2560, h2566, h2570, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2810_1, u0elo3]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h3, hlam, p2810_0]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            rcases p2810_3 (m.d 0 1) (by simp) with h2862 | h2862
                            · rcases p2810_3 (m.d 0 2) (by simp) with h2863 | h2863
                              · linarith only [h1371, h2863, hlam]
                              · rcases p2810_3 (m.d 0 3) (by simp) with h2865 | h2865
                                · linarith only [h2443, h2865, hlam]
                                · linarith only [h2865, h4, hlam]
                            · linarith only [h0, h2862, hlam]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            rcases p2810_3 (m.d 0 1) (by simp) with h2869 | h2869
                            · rcases p2810_3 (m.d 0 2) (by simp) with h2870 | h2870
                              · linarith only [h1371, h2870, hlam]
                              · rcases p2810_3 (m.d 0 3) (by simp) with h2872 | h2872
                                · linarith only [h2443, h2872, hlam]
                                · rcases p2810_3 (m.d 0 4) (by simp) with h2874 | h2874
                                  · rcases p2810_3 (m.d 0 5) (by simp) with h2875 | h2875
                                    · rcases h2bigk with h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h2806, h2809, h4, hc12, hc34, hlam, hphi, ht23, p2876_1]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h4, hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h1025, hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h1371, hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h0, hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h2560, hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h2562, hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h2564, hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h2806, h2809, hc02, hc34, hlam, hphi, ht23, p2876_1]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h2806, h2809, hc12, hc34, hlam, hphi, ht23, p2876_1]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h2804, hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h2806, hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        rcases p2876_3 (m.d 0 2) (by simp) with h2892 | h2892
                                        · linarith only [h2892, hlam, p2876_0]
                                        · rcases p2876_3 (m.d 1 2) (by simp) with h2894 | h2894
                                          · linarith only [h2562, h2894, hlam]
                                          · rcases p2876_3 (m.d 2 3) (by simp) with h2896 | h2896
                                            · linarith only [h2804, h2896, hlam]
                                            · linarith only [h2896, h4, hlam]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        rcases p2876_3 (m.d 0 2) (by simp) with h2899 | h2899
                                        · linarith only [h1025, h2899, hlam]
                                        · linarith only [h0, h2899, hlam]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h0, h4, hc12, hc24, hlam, hphi, p2876_1]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h0, h1371, hc12, hc24, hlam, hphi, p2876_1]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        rcases p2876_3 (m.d 0 2) (by simp) with h2905 | h2905
                                        · linarith only [h2905, hlam, p2876_0]
                                        · rcases p2876_3 (m.d 1 2) (by simp) with h2907 | h2907
                                          · linarith only [h2564, h2907, hlam]
                                          · rcases p2876_3 (m.d 2 3) (by simp) with h2909 | h2909
                                            · linarith only [h2806, h2909, hlam]
                                            · linarith only [h2909, h4, hlam]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        rcases p2876_3 (m.d 0 2) (by simp) with h2912 | h2912
                                        · linarith only [h1371, h2912, hlam]
                                        · linarith only [h0, h2912, hlam]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p2876_1]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [h2808, hlam, p2876_0]
                                      · have p2876_0 := h2876c.1
                                        have p2876_1 := h2876c.2.1
                                        have p2876_2 := h2876c.2.2.1
                                        have p2876_3 := h2876c.2.2.2
                                        linarith only [hlam, p2876_0]
                                    · linarith only [h2443, h2875, hlam]
                                  · linarith only [h1499, h2874, hlam]
                            · linarith only [h1, h2869, hlam]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [h2559, hlam, p2810_1]
                          · have p2810_0 := h2810c.1
                            have p2810_1 := h2810c.2.1
                            have p2810_2 := h2810c.2.2.1
                            have p2810_3 := h2810c.2.2.2
                            linarith only [hlam, p2810_0]
                        · linarith only [h1025, h2559, h2804, h2809, hlam]
                      · linarith only [h1025, h2559, h2808, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2925 | h2925
      · linarith only [h0, h2925, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2927 | h2927
        · linarith only [h0, h1025, h2927, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2929 | h2929
          · linarith only [h0, h1371, h2929, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2931 | h2931
            · linarith only [h1, h1499, h2931, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2933 | h2933
              · linarith only [h1, h2443, h2933, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2935 | h2935
                · linarith only [h2, h2559, h2935, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2937 | h2937
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2938 | h2938
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2939 | h2939
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2940 | h2940
                        · linarith only [h0, h1025, h2559, h2937, h2940, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1499, h2939, h2940, h4, hc12, hc24, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2943 | h2943
                        · linarith only [h0, h1025, h2939, h2943, hc12, hc34, hlam, hphi, ht23]
                        · rcases h0bigk with h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c | h2945c
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [hlam, p2945_0]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            rcases p2945_3 (m.d 0 1) (by simp) with h2947 | h2947
                            · rcases p2945_3 (m.d 0 2) (by simp) with h2948 | h2948
                              · linarith only [h0, h2948, hlam]
                              · rcases p2945_3 (m.d 0 3) (by simp) with h2950 | h2950
                                · linarith only [h1, h2950, hlam]
                                · linarith only [h2950, h4, hlam]
                            · linarith only [h0, h2947, hlam]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            rcases p2945_3 (m.d 0 1) (by simp) with h2954 | h2954
                            · rcases p2945_3 (m.d 0 2) (by simp) with h2955 | h2955
                              · linarith only [h0, h2955, hlam]
                              · rcases p2945_3 (m.d 0 3) (by simp) with h2957 | h2957
                                · linarith only [h1, h2957, hlam]
                                · rcases p2945_3 (m.d 0 4) (by simp) with h2959 | h2959
                                  · linarith only [h2, h2959, hlam]
                                  · linarith only [h1499, h2959, hlam]
                            · linarith only [h1, h2954, hlam]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            rcases p2945_3 (m.d 0 1) (by simp) with h2963 | h2963
                            · rcases p2945_3 (m.d 0 2) (by simp) with h2964 | h2964
                              · linarith only [h0, h2964, hlam]
                              · rcases p2945_3 (m.d 0 3) (by simp) with h2966 | h2966
                                · linarith only [h1, h2966, hlam]
                                · rcases p2945_3 (m.d 0 4) (by simp) with h2968 | h2968
                                  · linarith only [h2, h2968, hlam]
                                  · rcases p2945_3 (m.d 0 5) (by simp) with h2970 | h2970
                                    · linarith only [h2970, h3, hlam]
                                    · linarith only [h2559, h2970, hlam]
                            · linarith only [h2, h2963, hlam]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            rcases p2945_3 (m.d 0 1) (by simp) with h2974 | h2974
                            · rcases p2945_3 (m.d 0 2) (by simp) with h2975 | h2975
                              · linarith only [h0, h2975, hlam]
                              · rcases p2945_3 (m.d 0 3) (by simp) with h2977 | h2977
                                · linarith only [h1, h2977, hlam]
                                · rcases p2945_3 (m.d 0 4) (by simp) with h2979 | h2979
                                  · linarith only [h2, h2979, hlam]
                                  · rcases p2945_3 (m.d 0 5) (by simp) with h2981 | h2981
                                    · linarith only [h2981, h3, hlam]
                                    · rcases h2bigk with h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c | h2983c
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h1499, h2937, h4, hc12, hc24, hlam, hphi, p2983_1]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h4, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h1025, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h1371, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h0, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2925, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2927, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2929, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        rcases p2983_3 (m.d 0 2) (by simp) with h2994 | h2994
                                        · linarith only [h2994, hlam, p2983_0]
                                        · rcases p2983_3 (m.d 1 2) (by simp) with h2996 | h2996
                                          · linarith only [h2925, h2996, hlam]
                                          · rcases p2983_3 (m.d 2 3) (by simp) with h2998 | h2998
                                            · rcases p2983_3 (m.d 2 4) (by simp) with h2999 | h2999
                                              · linarith only [h2937, h2999, hlam]
                                              · linarith only [h1025, h2999, hlam]
                                            · linarith only [h2998, hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        rcases p2983_3 (m.d 0 2) (by simp) with h3003 | h3003
                                        · linarith only [h3003, h4, hlam]
                                        · linarith only [h0, h3003, hlam]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h1025, hc02, hc23, hlam, hphi, p2983_1]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h0, h1371, hc12, hc23, hlam, hphi, p2983_1]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h0, h2939, hc12, hc45, hlam, hphi, ht23, ht34, p2983_1]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2939, hc12, hc45, hlam, hphi, ht23, ht34, p2983_1]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2937, hlam, p2983_1]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [hlam, p2983_0]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2939, hlam, p2983_1]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        rcases p2983_3 (m.d 0 2) (by simp) with h3014 | h3014
                                        · linarith only [h3014, hlam, p2983_0]
                                        · rcases p2983_3 (m.d 1 2) (by simp) with h3016 | h3016
                                          · linarith only [h2929, h3016, hlam]
                                          · rcases p2983_3 (m.d 2 3) (by simp) with h3018 | h3018
                                            · rcases p2983_3 (m.d 2 4) (by simp) with h3019 | h3019
                                              · linarith only [h2939, h3019, hlam]
                                              · linarith only [h1025, h3019, hlam]
                                            · linarith only [h3018, h4, hlam]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        rcases p2983_3 (m.d 0 2) (by simp) with h3023 | h3023
                                        · linarith only [h1371, h3023, hlam]
                                        · linarith only [h0, h3023, hlam]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h2938, hlam, p2983_1]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [h0, h1025, hc12, hc25, hlam, hphi, p2983_1]
                                      · have p2983_0 := h2983c.1
                                        have p2983_1 := h2983c.2.1
                                        have p2983_2 := h2983c.2.2.1
                                        have p2983_3 := h2983c.2.2.2
                                        linarith only [hlam, p2983_0]
                            · linarith only [h2974, h3, hlam]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h0, hlam, p2945_0]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [hlam, p2945_0]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h4, hlam, p2945_0]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h1025, hlam, p2945_1]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h1371, hlam, p2945_0]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h1, hlam, p2945_1]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h0, h1499, hc12, hc34, hlam, hphi, ht23, p2945_1]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [hlam, p2945_0]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h1499, hlam, p2945_1]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h2443, hlam, p2945_1]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h2, hlam, p2945_0]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h0, h2443, h2559, h2938, hc12, hc23, hlam, hphi, p2945_1]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h1, h2443, h2559, h2925, h2938, hc12, hc23, hlam, hphi, p2945_1]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [hlam, p2945_0]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h2559, hlam, p2945_0]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h3, hlam, p2945_0]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h0, h2443, h2938, hc12, hc23, hlam, hphi, p2945_1]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h1, h2443, h2925, h2938, hc12, hc23, hlam, hphi, p2945_1]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [h2, h2443, h2925, h2931, h2938, hc12, hc23, hlam, hphi, p2945_1]
                          · have p2945_0 := h2945c.1
                            have p2945_1 := h2945c.2.1
                            have p2945_2 := h2945c.2.2.1
                            have p2945_3 := h2945c.2.2.2
                            linarith only [hlam, p2945_0]
                    · linarith only [h1, h1499, h2925, h2937, h2938, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3051 | h3051
                    · linarith only [h1, h2443, h2925, h2937, h3051, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3053 | h3053
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3054 | h3054
                        · rcases h0bigk with h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c | h3055c
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [hlam, p3055_0]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            rcases p3055_3 (m.d 0 1) (by simp) with h3057 | h3057
                            · rcases p3055_3 (m.d 0 2) (by simp) with h3058 | h3058
                              · linarith only [h0, h3058, hlam]
                              · rcases p3055_3 (m.d 0 3) (by simp) with h3060 | h3060
                                · linarith only [h1, h3060, hlam]
                                · linarith only [h3060, h4, hlam]
                            · linarith only [h0, h3057, hlam]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            rcases p3055_3 (m.d 0 1) (by simp) with h3064 | h3064
                            · rcases p3055_3 (m.d 0 2) (by simp) with h3065 | h3065
                              · linarith only [h0, h3065, hlam]
                              · rcases p3055_3 (m.d 0 3) (by simp) with h3067 | h3067
                                · linarith only [h1, h3067, hlam]
                                · rcases p3055_3 (m.d 0 4) (by simp) with h3069 | h3069
                                  · linarith only [h2, h3069, hlam]
                                  · linarith only [h1499, h3069, hlam]
                            · linarith only [h1, h3064, hlam]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            rcases p3055_3 (m.d 0 1) (by simp) with h3073 | h3073
                            · rcases p3055_3 (m.d 0 2) (by simp) with h3074 | h3074
                              · linarith only [h0, h3074, hlam]
                              · rcases p3055_3 (m.d 0 3) (by simp) with h3076 | h3076
                                · linarith only [h1, h3076, hlam]
                                · rcases p3055_3 (m.d 0 4) (by simp) with h3078 | h3078
                                  · linarith only [h2, h3078, hlam]
                                  · rcases p3055_3 (m.d 0 5) (by simp) with h3080 | h3080
                                    · linarith only [h3, h3080, hlam]
                                    · linarith only [h2559, h3080, hlam]
                            · linarith only [h2, h3073, hlam]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            rcases p3055_3 (m.d 0 1) (by simp) with h3084 | h3084
                            · rcases p3055_3 (m.d 0 2) (by simp) with h3085 | h3085
                              · linarith only [h0, h3085, hlam]
                              · rcases p3055_3 (m.d 0 3) (by simp) with h3087 | h3087
                                · linarith only [h1, h3087, hlam]
                                · rcases p3055_3 (m.d 0 4) (by simp) with h3089 | h3089
                                  · linarith only [h2, h3089, hlam]
                                  · rcases p3055_3 (m.d 0 5) (by simp) with h3091 | h3091
                                    · linarith only [h3, h3091, hlam]
                                    · rcases h2bigk with h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c | h3093c
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h3051, h3054, h4, hc12, hc34, hlam, hphi, ht23, p3093_1]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h4, hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h1025, hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h1371, hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h0, hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h2925, hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h2927, hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h2929, hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h3051, h3054, hc02, hc34, hlam, hphi, ht23, p3093_1]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h3051, h3054, hc12, hc34, hlam, hphi, ht23, p3093_1]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h2937, hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h3051, hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        rcases p3093_3 (m.d 0 2) (by simp) with h3109 | h3109
                                        · linarith only [h3109, hlam, p3093_0]
                                        · rcases p3093_3 (m.d 1 2) (by simp) with h3111 | h3111
                                          · linarith only [h2927, h3111, hlam]
                                          · rcases p3093_3 (m.d 2 3) (by simp) with h3113 | h3113
                                            · linarith only [h2937, h3113, hlam]
                                            · linarith only [h3113, h4, hlam]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        rcases p3093_3 (m.d 0 2) (by simp) with h3116 | h3116
                                        · linarith only [h1025, h3116, hlam]
                                        · linarith only [h0, h3116, hlam]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h0, h2937, h4, hc12, hc34, hlam, hphi, ht23, p3093_1]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h0, h1371, h2937, hc12, hc34, hlam, hphi, ht23, p3093_1]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        rcases p3093_3 (m.d 0 2) (by simp) with h3122 | h3122
                                        · linarith only [h3122, hlam, p3093_0]
                                        · rcases p3093_3 (m.d 1 2) (by simp) with h3124 | h3124
                                          · linarith only [h2929, h3124, hlam]
                                          · rcases p3093_3 (m.d 2 3) (by simp) with h3126 | h3126
                                            · linarith only [h3051, h3126, hlam]
                                            · linarith only [h3126, h4, hlam]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        rcases p3093_3 (m.d 0 2) (by simp) with h3129 | h3129
                                        · linarith only [h1371, h3129, hlam]
                                        · linarith only [h0, h3129, hlam]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p3093_1]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [h3053, hlam, p3093_0]
                                      · have p3093_0 := h3093c.1
                                        have p3093_1 := h3093c.2.1
                                        have p3093_2 := h3093c.2.2.1
                                        have p3093_3 := h3093c.2.2.2
                                        linarith only [hlam, p3093_0]
                            · linarith only [h3, h3084, hlam]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h0, hlam, p3055_0]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [hlam, p3055_0]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h4, hlam, p3055_0]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h1025, hlam, p3055_1]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h1371, hlam, p3055_0]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h1, hlam, p3055_1]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h0, h1499, hc12, hc34, hlam, hphi, ht23, p3055_1]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [hlam, p3055_0]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h1499, hlam, p3055_1]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h2443, hlam, p3055_1]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h2, hlam, p3055_0]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h0, h2559, hc12, hc45, hlam, hphi, ht23, ht34, p3055_1]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h2559, hc03, hc45, hlam, hphi, ht34, p3055_1]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [hlam, p3055_0]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h2559, hlam, p3055_0]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h3, hlam, p3055_0]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h0, h2559, h2937, h3053, hc12, hc34, hlam, hphi, ht23, p3055_1]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h1, h2559, h2925, h2937, h3053, hc12, hc34, hlam, hphi, ht23, p3055_1]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [h2, h2559, h2925, h2931, h2937, h3053, hc12, hc34, hlam, hphi, ht23, p3055_1]
                          · have p3055_0 := h3055c.1
                            have p3055_1 := h3055c.2.1
                            have p3055_2 := h3055c.2.2.1
                            have p3055_3 := h3055c.2.2.2
                            linarith only [hlam, p3055_0]
                        · linarith only [h2937, h3053, h3054, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3157 | h3157
                        · linarith only [h0, h2937, h3053, h3157, h4, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h2937, h3157, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1025 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1371 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h1499 | h1499
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1025 h1371 h1499
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1025 h1371 h1499

set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1025 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1371 | h1371
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1025 h1371
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1025 h1371

set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h1025 | h1025
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1025
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1025

set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 6560000 in
set_option maxHeartbeats 6560000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s2 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3160 | h3160
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3161 | h3161
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3162 | h3162
        · linarith only [h0, h3, h3162, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3164 | h3164
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3165 | h3165
            · linarith only [h1, h3, h3165, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3167 | h3167
              · linarith only [h2, h3, h3167, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3169 | h3169
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3170 | h3170
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3171 | h3171
                    · linarith only [h0, h3162, h3171, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3173 | h3173
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3174 | h3174
                        · linarith only [h0, h3, h3165, h3169, h3174, hlam]
                        · linarith only [h0, h3, h3169, h3174, hc23, hc35, hlam, hphi]
                      · linarith only [h3164, h3165, h3173, hc13, hc35, hlam, hphi]
                  · linarith only [h3161, h3162, h3170, hc12, hc25, hlam, hphi]
                · linarith only [h3160, h3162, h3169, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3180 | h3180
            · linarith only [h1, h3, h3180, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3182 | h3182
              · linarith only [h0, h3, h3161, h3182, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3184 | h3184
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3185 | h3185
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3186 | h3186
                    · linarith only [h0, h3162, h3186, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3188 | h3188
                      · linarith only [h1, h3164, h3188, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3190 | h3190
                        · linarith only [h0, h1, h3, h3180, h3185, h3190, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h0, h3, h3184, h3190, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h3161, h3184, h3185, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h3160, h3162, h3184, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3195 | h3195
        · linarith only [h2, h3, h3161, h3195, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3197 | h3197
          · linarith only [h3160, h3161, h3197, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3199 | h3199
            · linarith only [h1, h3, h3199, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3201 | h3201
              · linarith only [h2, h3, h3201, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3203 | h3203
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3204 | h3204
                  · linarith only [h0, h3161, h3204, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3206 | h3206
                    · linarith only [h0, h3, h3195, h3206, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3208 | h3208
                      · linarith only [h1, h3197, h3208, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3210 | h3210
                        · linarith only [h0, h1, h3, h3199, h3203, h3210, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h2, h3, h3203, h3204, h3210, hc23, hc35, hlam, hphi]
                · linarith only [h3160, h3161, h3201, h3203, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3214 | h3214
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3215 | h3215
        · linarith only [h1, h3, h3160, h3215, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3217 | h3217
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3218 | h3218
            · linarith only [h1, h3, h3218, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3220 | h3220
              · linarith only [h2, h3, h3220, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3222 | h3222
                · linarith only [h0, h3160, h3222, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3224 | h3224
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3225 | h3225
                    · linarith only [h0, h3, h3215, h3225, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3227 | h3227
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3228 | h3228
                        · linarith only [h1, h3, h3218, h3228, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3230 | h3230
                          · linarith only [h1, h3, h3220, h3222, h3224, h3230, hlam]
                          · linarith only [h1, h3, h3227, h3230, hc34, hc45, hlam, hphi]
                      · linarith only [h3217, h3222, h3224, h3227, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h3160, h3214, h3224, hc12, hc23, hlam, hphi]
          · linarith only [h3160, h3214, h3217, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3236 | h3236
        · linarith only [h0, h3, h3236, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3238 | h3238
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3239 | h3239
            · linarith only [h1, h3, h3239, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3241 | h3241
              · linarith only [h1, h3, h3238, h3241, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3243 | h3243
                · linarith only [h0, h3160, h3243, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3245 | h3245
                  · linarith only [h0, h3214, h3245, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3247 | h3247
                    · linarith only [h0, h3, h3236, h3247, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3249 | h3249
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3250 | h3250
                        · linarith only [h1, h3214, h3238, h3239, h3250, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3252 | h3252
                          · linarith only [h2, h3241, h3252, hlam]
                          · linarith only [h1, h3, h3249, h3252, hc34, hc45, hlam, hphi]
                      · linarith only [h3238, h3239, h3249, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3256 | h3256
            · linarith only [h2, h3, h3238, h3256, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3258 | h3258
              · linarith only [h2, h3, h3258, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3260 | h3260
                · linarith only [h0, h3160, h3260, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3262 | h3262
                  · linarith only [h0, h3214, h3262, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3264 | h3264
                    · linarith only [h0, h3236, h3264, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3266 | h3266
                      · linarith only [h1, h3, h3238, h3264, h3266, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3268 | h3268
                        · linarith only [h2, h3, h3256, h3266, h3268, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3270 | h3270
                          · linarith only [h2, h3, h3258, h3268, h3270, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3272 | h3272
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3273 | h3273
                              · linarith only [h2, h3, h3260, h3266, h3268, h3273, hc12, hc23, hlam, hphi]
                              · linarith only [h1, h3238, h3260, h3272, h3273, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3276 | h3276
                              · linarith only [h1, h3256, h3260, h3272, h3276, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3278 | h3278
                                · linarith only [h2, h3, h3260, h3266, h3270, h3278, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3280 | h3280
                                  · linarith only [h0, h3160, h3272, h3278, h3280, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h3160, h3272, h3280, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
