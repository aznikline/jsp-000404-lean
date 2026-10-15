import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S2
import Jsp000404.R1LeavesN7_22S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 3 5 (by decide) (by decide) with h2374 | h2374
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2375 | h2375
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2376 | h2376
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2377 | h2377
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2378 | h2378
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2379 | h2379
            · rcases h0bigk with h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c | h2380c
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [hlam, p2380_0]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                rcases p2380_3 (m.d 0 1) (by simp) with h2382 | h2382
                · rcases p2380_3 (m.d 0 2) (by simp) with h2383 | h2383
                  · linarith only [h0, h2383, hlam]
                  · rcases p2380_3 (m.d 0 3) (by simp) with h2385 | h2385
                    · linarith only [h1, h2385, hlam]
                    · linarith only [h2385, h4, hlam]
                · linarith only [h0, h2382, hlam]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h1558, h1561, h1565, h1566, h2377, h2379, hc01, hc45, hlam, hphi, ht0b, ht5b, p2380_1]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h1558, h1561, h1565, h1566, h2377, h2379, hc01, hc45, hlam, hphi, ht0b, ht5b, p2380_1]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                rcases p2380_3 (m.d 0 1) (by simp) with h2391 | h2391
                · rcases p2380_3 (m.d 0 2) (by simp) with h2392 | h2392
                  · linarith only [h0, h2392, hlam]
                  · linarith only [h1557, h2392, hlam]
                · linarith only [h2391, h3, hlam]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h0, hlam, p2380_0]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [hlam, p2380_0]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h4, hlam, p2380_0]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h1385, hlam, p2380_1]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                rcases p2380_3 (m.d 0 1) (by simp) with h2400 | h2400
                · rcases p2380_3 (m.d 0 2) (by simp) with h2401 | h2401
                  · rcases p2380_3 (m.d 0 3) (by simp) with h2402 | h2402
                    · rcases p2380_3 (m.d 0 4) (by simp) with h2403 | h2403
                      · rcases p2380_3 (m.d 0 5) (by simp) with h2404 | h2404
                        · linarith only [h1557, h2404, hlam]
                        · rcases h0emin with h2406 | h2406 | h2406 | h2406 | h2406
                          · rcases h2bigk with h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c | h2407c
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h1385, h1565, h2376, h2377, h2379, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2407_1]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h4, hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h1385, hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              rcases p2407_3 (m.d 0 2) (by simp) with h2412 | h2412
                              · rcases p2407_3 (m.d 1 2) (by simp) with h2413 | h2413
                                · linarith only [h0, h2413, hlam]
                                · linarith only [h1565, h2413, hlam]
                              · linarith only [h2412, hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h0, hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h1561, hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h1563, hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h1558, h1561, h1566, h2377, h2379, hc03, hc45, hlam, hphi, ht0b, ht5b, p2407_1]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2407_1]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              rcases p2407_3 (m.d 0 2) (by simp) with h2423 | h2423
                              · linarith only [h2423, h4, hlam]
                              · linarith only [h0, h2423, hlam]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h1385, h1565, h2377, h2379, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2407_1]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h1565, h3, h4, hlam, p2380_1, p2407_2]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2407_1]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              rcases p2407_3 (m.d 0 2) (by simp) with h2430 | h2430
                              · linarith only [h1385, h2430, hlam]
                              · linarith only [h0, h2430, hlam]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h2376, hlam, p2407_1]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h1385, h1565, h3, hlam, p2380_1, p2407_2]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h1557, hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h1565, hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h2377, hlam, p2407_1]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [h2378, hlam, p2407_0]
                            · have p2407_0 := h2407c.1
                              have p2407_1 := h2407c.2.1
                              have p2407_2 := h2407c.2.2.1
                              have p2407_3 := h2407c.2.2.2
                              linarith only [hlam, p2407_0]
                          · linarith only [h1385, h2376, h2406, hc23, hlam, ht01, ht12]
                          · rcases h2bigk with h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c | h2442c
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h1385, h2376, hc12, hc23, hlam, hphi, p2442_1]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h4, hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h1385, hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              rcases p2442_3 (m.d 0 2) (by simp) with h2447 | h2447
                              · rcases p2442_3 (m.d 1 2) (by simp) with h2448 | h2448
                                · linarith only [h0, h2448, hlam]
                                · linarith only [h1565, h2448, hlam]
                              · linarith only [h2447, hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h0, hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h1561, hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h1563, hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h1558, h1561, h1566, h2377, h2379, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2442_1]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h1565, h2377, h2379, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2442_1]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              rcases p2442_3 (m.d 0 2) (by simp) with h2458 | h2458
                              · linarith only [h2458, h4, hlam]
                              · linarith only [h0, h2458, hlam]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h1385, h1565, h2377, h2379, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2442_1]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h1565, h3, h4, hlam, p2380_1, p2442_2]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2442_1]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              rcases p2442_3 (m.d 0 2) (by simp) with h2465 | h2465
                              · linarith only [h1385, h2465, hlam]
                              · linarith only [h0, h2465, hlam]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h2376, hlam, p2442_1]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h1385, h1565, h3, hlam, p2380_1, p2442_2]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h1557, hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h1565, hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h2377, hlam, p2442_1]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [h2378, hlam, p2442_0]
                            · have p2442_0 := h2442c.1
                              have p2442_1 := h2442c.2.1
                              have p2442_2 := h2442c.2.2.1
                              have p2442_3 := h2442c.2.2.2
                              linarith only [hlam, p2442_0]
                          · rcases h2bigk with h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c | h2476c
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h1385, h1565, h2377, h2379, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2476_1]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h4, hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h1385, hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              rcases p2476_3 (m.d 0 2) (by simp) with h2481 | h2481
                              · rcases p2476_3 (m.d 1 2) (by simp) with h2482 | h2482
                                · linarith only [h0, h2482, hlam]
                                · linarith only [h1565, h2482, hlam]
                              · linarith only [h2481, hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h0, hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h1561, hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h1563, hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h1558, h1561, h1566, h2377, h2379, hc03, hc45, hlam, hphi, ht0b, ht5b, p2476_1]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h1565, h2377, h2379, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2476_1]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              rcases p2476_3 (m.d 0 2) (by simp) with h2492 | h2492
                              · linarith only [h2492, h4, hlam]
                              · linarith only [h0, h2492, hlam]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h1385, h1565, h2377, h2379, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2476_1]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h1565, h3, h4, hlam, p2380_1, p2476_2]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h1565, h2377, h2379, h3, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2476_1]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              rcases p2476_3 (m.d 0 2) (by simp) with h2499 | h2499
                              · linarith only [h1385, h2499, hlam]
                              · linarith only [h0, h2499, hlam]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h2376, hlam, p2476_1]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h1385, h1565, h3, hlam, p2380_1, p2476_2]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h1557, hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h1565, hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h2377, hlam, p2476_1]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [h2378, hlam, p2476_0]
                            · have p2476_0 := h2476c.1
                              have p2476_1 := h2476c.2.1
                              have p2476_2 := h2476c.2.2.1
                              have p2476_3 := h2476c.2.2.2
                              linarith only [hlam, p2476_0]
                          · linarith only [h2406, hc02, hlam, p2380_1]
                      · linarith only [h1560, h2403, hlam]
                    · linarith only [h1559, h2402, hlam]
                  · linarith only [h1557, h2401, hlam]
                · linarith only [h2400, h3, hlam]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h1, hlam, p2380_1]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                rcases p2380_3 (m.d 0 1) (by simp) with h2516 | h2516
                · rcases p2380_3 (m.d 0 2) (by simp) with h2517 | h2517
                  · linarith only [h2517, h4, hlam]
                  · rcases p2380_3 (m.d 0 3) (by simp) with h2519 | h2519
                    · rcases p2380_3 (m.d 0 4) (by simp) with h2520 | h2520
                      · linarith only [h1558, h2520, hlam]
                      · linarith only [h1385, h2520, hlam]
                    · linarith only [h2519, h4, hlam]
                · linarith only [h0, h2516, hlam]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [hlam, p2380_0]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h1558, h1561, h1565, h1566, h2377, h2379, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                rcases p2380_3 (m.d 0 1) (by simp) with h2527 | h2527
                · rcases p2380_3 (m.d 0 2) (by simp) with h2528 | h2528
                  · linarith only [h2528, h4, hlam]
                  · linarith only [h1557, h2528, hlam]
                · linarith only [h2527, h3, hlam]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h2, hlam, p2380_0]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                rcases p2380_3 (m.d 0 1) (by simp) with h2533 | h2533
                · rcases p2380_3 (m.d 0 2) (by simp) with h2534 | h2534
                  · linarith only [h1385, h2534, hlam]
                  · rcases p2380_3 (m.d 0 3) (by simp) with h2536 | h2536
                    · rcases p2380_3 (m.d 0 4) (by simp) with h2537 | h2537
                      · rcases p2380_3 (m.d 0 5) (by simp) with h2538 | h2538
                        · linarith only [h1560, h2538, hlam]
                        · rcases h0emin with h2540 | h2540 | h2540 | h2540 | h2540
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
                              linarith only [h1565, h2377, h2379, hc04, hc45, hlam, hphi, ht0b, ht5b, p2380_1, p2541_1]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h4, hlam, p2541_0]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h1385, hlam, p2541_0]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h1385, h2376, h2377, h2379, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2541_1]
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
                              linarith only [h1561, hlam, p2541_0]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h1563, hlam, p2541_0]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h0, h1385, h2376, h2377, h2379, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2541_1]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              rcases p2541_3 (m.d 0 2) (by simp) with h2552 | h2552
                              · linarith only [h2552, hlam, p2541_0]
                              · rcases p2541_3 (m.d 1 2) (by simp) with h2554 | h2554
                                · linarith only [h1561, h2554, hlam]
                                · rcases p2541_3 (m.d 2 3) (by simp) with h2556 | h2556
                                  · rcases p2541_3 (m.d 2 4) (by simp) with h2557 | h2557
                                    · linarith only [h2376, h2557, hlam]
                                    · linarith only [h1385, h2557, hlam]
                                  · linarith only [h2556, hlam, p2541_0]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              rcases p2541_3 (m.d 0 2) (by simp) with h2561 | h2561
                              · linarith only [h2561, h4, hlam]
                              · linarith only [h0, h2561, hlam]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [hlam, p2541_0]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h1385, hc02, hc23, hlam, hphi, p2380_1, p2541_1]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h1558, h1561, h1565, h1566, h4, hlam, p2541_2]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              rcases p2541_3 (m.d 0 2) (by simp) with h2567 | h2567
                              · linarith only [h2567, hlam, p2541_0]
                              · rcases p2541_3 (m.d 1 2) (by simp) with h2569 | h2569
                                · linarith only [h1563, h2569, hlam]
                                · rcases p2541_3 (m.d 2 3) (by simp) with h2571 | h2571
                                  · rcases p2541_3 (m.d 2 4) (by simp) with h2572 | h2572
                                    · rcases p2541_3 (m.d 2 5) (by simp) with h2573 | h2573
                                      · linarith only [h2378, h2573, hlam]
                                      · rcases h3bigk with h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c | h2575c
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [hlam, p2575_0]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          rcases p2575_3 (m.d 0 3) (by simp) with h2577 | h2577
                                          · rcases p2575_3 (m.d 1 3) (by simp) with h2578 | h2578
                                            · linarith only [h1, h2578, hlam]
                                            · rcases p2575_3 (m.d 2 3) (by simp) with h2580 | h2580
                                              · rcases p2575_3 (m.d 3 4) (by simp) with h2581 | h2581
                                                · linarith only [h1558, h2581, hlam]
                                                · linarith only [h1566, h2581, hlam]
                                              · linarith only [h1561, h2580, hlam]
                                          · linarith only [h1, h2577, hlam]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h4, hlam, p2575_1]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h1561, h1565, h1566, h2377, h2379, hc03, hc45, hlam, hphi, ht0b, ht5b, p2575_1]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h1558, h1561, h1565, h1566, h2377, hlam, p2575_2]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h1, hlam, p2575_0]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [hlam, p2575_0]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h1561, hlam, p2575_1]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h1566, hlam, p2575_0]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h1558, h1566, h2379, hc03, hc45, hlam, hphi, ht0b, ht5b, p2575_1]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h1558, h1566, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2575_1]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          rcases p2575_3 (m.d 0 3) (by simp) with h2595 | h2595
                                          · linarith only [h2595, h4, hlam]
                                          · linarith only [h1, h2595, hlam]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [hlam, p2575_0]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h1561, h1565, h1566, h2377, h2379, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2575_1]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h0, h1558, h1565, h2377, h4, hlam, p2380_1, p2575_2]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h1558, hlam, p2575_0]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h1558, h1561, h1565, h2377, h2379, hc03, hc45, hlam, hphi, ht0b, ht5b, p2575_1]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h2376, hlam, p2575_0]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [hlam, p2575_0]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          rcases p2575_3 (m.d 0 3) (by simp) with h2605 | h2605
                                          · rcases p2575_3 (m.d 1 3) (by simp) with h2606 | h2606
                                            · linarith only [h1566, h2606, hlam]
                                            · linarith only [h2374, h2606, hlam]
                                          · linarith only [h1559, h2605, hlam]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h1559, hlam, p2575_0]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h2374, hlam, p2575_0]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h2377, hlam, p2575_0]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [h2379, hlam, p2575_0]
                                        · have p2575_0 := h2575c.1
                                          have p2575_1 := h2575c.2.1
                                          have p2575_2 := h2575c.2.2.1
                                          have p2575_3 := h2575c.2.2.2
                                          linarith only [hlam, p2575_0]
                                    · linarith only [h2572, hlam, p2541_0]
                                  · linarith only [h2571, h4, hlam]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              rcases p2541_3 (m.d 0 2) (by simp) with h2617 | h2617
                              · linarith only [h1385, h2617, hlam]
                              · linarith only [h0, h2617, hlam]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h2376, hlam, p2541_1]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [hlam, p2541_0]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h0, h1385, h1565, hlam, p2380_1, p2541_2]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h1557, hlam, p2541_0]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h1565, hlam, p2541_0]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h2377, hlam, p2541_1]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [h2378, hlam, p2541_0]
                            · have p2541_0 := h2541c.1
                              have p2541_1 := h2541c.2.1
                              have p2541_2 := h2541c.2.2.1
                              have p2541_3 := h2541c.2.2.2
                              linarith only [hlam, p2541_0]
                          · linarith only [h2540, hc04, hlam, p2380_1]
                          · rcases h2bigk with h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c | h2629c
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h1558, h1565, h2377, h2379, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2629_1]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h4, hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h1385, hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h1558, h2377, h2379, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2629_1]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h0, hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h1561, hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h1563, hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h0, h1558, h2377, h2379, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2629_1]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              rcases p2629_3 (m.d 0 2) (by simp) with h2640 | h2640
                              · linarith only [h2640, hlam, p2629_0]
                              · rcases p2629_3 (m.d 1 2) (by simp) with h2642 | h2642
                                · linarith only [h1561, h2642, hlam]
                                · rcases p2629_3 (m.d 2 3) (by simp) with h2644 | h2644
                                  · rcases p2629_3 (m.d 2 4) (by simp) with h2645 | h2645
                                    · linarith only [h2376, h2645, hlam]
                                    · linarith only [h1385, h2645, hlam]
                                  · linarith only [h2644, hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              rcases p2629_3 (m.d 0 2) (by simp) with h2649 | h2649
                              · linarith only [h2649, h4, hlam]
                              · linarith only [h0, h2649, hlam]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h1385, hc02, hc23, hlam, hphi, p2629_1]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h0, h1558, h1565, h4, hlam, p2380_1, p2629_2]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              rcases p2629_3 (m.d 0 2) (by simp) with h2655 | h2655
                              · linarith only [h2655, hlam, p2629_0]
                              · rcases p2629_3 (m.d 1 2) (by simp) with h2657 | h2657
                                · linarith only [h1563, h2657, hlam]
                                · rcases p2629_3 (m.d 2 3) (by simp) with h2659 | h2659
                                  · rcases p2629_3 (m.d 2 4) (by simp) with h2660 | h2660
                                    · rcases p2629_3 (m.d 2 5) (by simp) with h2661 | h2661
                                      · linarith only [h2378, h2661, hlam]
                                      · rcases h3bigk with h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c | h2663c
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [hlam, p2663_0]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          rcases p2663_3 (m.d 0 3) (by simp) with h2665 | h2665
                                          · rcases p2663_3 (m.d 1 3) (by simp) with h2666 | h2666
                                            · linarith only [h1, h2666, hlam]
                                            · rcases p2663_3 (m.d 2 3) (by simp) with h2668 | h2668
                                              · rcases p2663_3 (m.d 3 4) (by simp) with h2669 | h2669
                                                · linarith only [h1558, h2669, hlam]
                                                · linarith only [h1566, h2669, hlam]
                                              · linarith only [h1561, h2668, hlam]
                                          · linarith only [h1, h2665, hlam]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h4, hlam, p2663_1]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h1561, h1565, h1566, h2377, h2379, hc03, hc45, hlam, hphi, ht0b, ht5b, p2663_1]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h1558, h1561, h1565, h1566, h2377, hlam, p2663_2]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h1, hlam, p2663_0]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [hlam, p2663_0]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h1561, hlam, p2663_1]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h1566, hlam, p2663_0]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h1558, h1566, h2379, hc03, hc45, hlam, hphi, ht0b, ht5b, p2663_1]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h2540, hc23, hlam, ht01, ht12, p2663_1]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          rcases p2663_3 (m.d 0 3) (by simp) with h2683 | h2683
                                          · linarith only [h2683, h4, hlam]
                                          · linarith only [h1, h2683, hlam]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [hlam, p2663_0]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h1561, h1565, h1566, h2377, h2379, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2663_1]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h0, h1558, h1565, h2377, h4, hlam, p2380_1, p2663_2]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h1558, hlam, p2663_0]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h1558, h1561, h1565, h2377, h2379, hc03, hc45, hlam, hphi, ht0b, ht5b, p2663_1]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h2376, hlam, p2663_0]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [hlam, p2663_0]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          rcases p2663_3 (m.d 0 3) (by simp) with h2693 | h2693
                                          · rcases p2663_3 (m.d 1 3) (by simp) with h2694 | h2694
                                            · linarith only [h1566, h2694, hlam]
                                            · linarith only [h2374, h2694, hlam]
                                          · linarith only [h1559, h2693, hlam]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h1559, hlam, p2663_0]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h2374, hlam, p2663_0]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h2377, hlam, p2663_0]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [h2379, hlam, p2663_0]
                                        · have p2663_0 := h2663c.1
                                          have p2663_1 := h2663c.2.1
                                          have p2663_2 := h2663c.2.2.1
                                          have p2663_3 := h2663c.2.2.2
                                          linarith only [hlam, p2663_0]
                                    · linarith only [h2660, hlam, p2629_0]
                                  · linarith only [h2659, h4, hlam]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              rcases p2629_3 (m.d 0 2) (by simp) with h2705 | h2705
                              · linarith only [h1385, h2705, hlam]
                              · linarith only [h0, h2705, hlam]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h2376, hlam, p2629_1]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h0, h1385, h1565, hlam, p2380_1, p2629_2]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h1557, hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h1565, hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h2377, hlam, p2629_1]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [h2378, hlam, p2629_0]
                            · have p2629_0 := h2629c.1
                              have p2629_1 := h2629c.2.1
                              have p2629_2 := h2629c.2.2.1
                              have p2629_3 := h2629c.2.2.2
                              linarith only [hlam, p2629_0]
                          · rcases h2bigk with h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c | h2716c
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h1565, h2377, h2379, hc04, hc45, hlam, hphi, ht0b, ht5b, p2380_1, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h4, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h1385, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h1385, h2377, h2379, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h0, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h1561, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h1563, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h0, h1385, h2377, h2379, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2380_1, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              rcases p2716_3 (m.d 0 2) (by simp) with h2727 | h2727
                              · linarith only [h2727, hlam, p2716_0]
                              · rcases p2716_3 (m.d 1 2) (by simp) with h2729 | h2729
                                · linarith only [h1561, h2729, hlam]
                                · rcases p2716_3 (m.d 2 3) (by simp) with h2731 | h2731
                                  · rcases p2716_3 (m.d 2 4) (by simp) with h2732 | h2732
                                    · linarith only [h2376, h2732, hlam]
                                    · linarith only [h1385, h2732, hlam]
                                  · linarith only [h2731, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              rcases p2716_3 (m.d 0 2) (by simp) with h2736 | h2736
                              · linarith only [h2736, h4, hlam]
                              · linarith only [h0, h2736, hlam]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h1385, hc02, hc23, hlam, hphi, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h0, h1558, h1565, h4, hlam, p2380_1, p2716_2]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              rcases p2716_3 (m.d 0 2) (by simp) with h2742 | h2742
                              · linarith only [h2742, hlam, p2716_0]
                              · rcases p2716_3 (m.d 1 2) (by simp) with h2744 | h2744
                                · linarith only [h1563, h2744, hlam]
                                · rcases p2716_3 (m.d 2 3) (by simp) with h2746 | h2746
                                  · rcases p2716_3 (m.d 2 4) (by simp) with h2747 | h2747
                                    · rcases p2716_3 (m.d 2 5) (by simp) with h2748 | h2748
                                      · linarith only [h2378, h2748, hlam]
                                      · rcases h3bigk with h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c | h2750c
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          rcases p2750_3 (m.d 0 3) (by simp) with h2752 | h2752
                                          · rcases p2750_3 (m.d 1 3) (by simp) with h2753 | h2753
                                            · linarith only [h1, h2753, hlam]
                                            · rcases p2750_3 (m.d 2 3) (by simp) with h2755 | h2755
                                              · rcases p2750_3 (m.d 3 4) (by simp) with h2756 | h2756
                                                · linarith only [h1558, h2756, hlam]
                                                · linarith only [h1566, h2756, hlam]
                                              · linarith only [h1561, h2755, hlam]
                                          · linarith only [h1, h2752, hlam]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h4, hlam, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h1561, h1565, h1566, h2377, h2379, hc03, hc45, hlam, hphi, ht0b, ht5b, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h1558, h1561, h1565, h1566, h2377, hlam, p2750_2]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h1, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h1561, hlam, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h1566, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h1558, h1566, h2379, hc03, hc45, hlam, hphi, ht0b, ht5b, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h1558, h1566, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          rcases p2750_3 (m.d 0 3) (by simp) with h2770 | h2770
                                          · linarith only [h2770, h4, hlam]
                                          · linarith only [h1, h2770, hlam]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h1561, h1565, h1566, h2377, h2379, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h0, h1558, h1565, h2377, h4, hlam, p2380_1, p2750_2]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h1558, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h1558, h1561, h1565, h2377, h2379, hc03, hc45, hlam, hphi, ht0b, ht5b, p2750_1]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2376, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          rcases p2750_3 (m.d 0 3) (by simp) with h2780 | h2780
                                          · rcases p2750_3 (m.d 1 3) (by simp) with h2781 | h2781
                                            · linarith only [h1566, h2781, hlam]
                                            · linarith only [h2374, h2781, hlam]
                                          · linarith only [h1559, h2780, hlam]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h1559, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2374, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2377, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [h2379, hlam, p2750_0]
                                        · have p2750_0 := h2750c.1
                                          have p2750_1 := h2750c.2.1
                                          have p2750_2 := h2750c.2.2.1
                                          have p2750_3 := h2750c.2.2.2
                                          linarith only [hlam, p2750_0]
                                    · linarith only [h2747, hlam, p2716_0]
                                  · linarith only [h2746, h4, hlam]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              rcases p2716_3 (m.d 0 2) (by simp) with h2792 | h2792
                              · linarith only [h1385, h2792, hlam]
                              · linarith only [h0, h2792, hlam]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2376, hlam, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h0, h1385, h1565, hlam, p2380_1, p2716_2]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h1557, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h1565, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2377, hlam, p2716_1]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [h2378, hlam, p2716_0]
                            · have p2716_0 := h2716c.1
                              have p2716_1 := h2716c.2.1
                              have p2716_2 := h2716c.2.2.1
                              have p2716_3 := h2716c.2.2.2
                              linarith only [hlam, p2716_0]
                          · linarith only [h2540, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                      · linarith only [h1385, h2537, hlam]
                    · linarith only [h2536, h4, hlam]
                · linarith only [h0, h2533, hlam]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h1558, hlam, p2380_0]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [hlam, p2380_0]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                rcases p2380_3 (m.d 0 1) (by simp) with h2809 | h2809
                · rcases p2380_3 (m.d 0 2) (by simp) with h2810 | h2810
                  · linarith only [h1385, h2810, hlam]
                  · linarith only [h1557, h2810, hlam]
                · linarith only [h2809, h3, hlam]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h3, hlam, p2380_0]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h1557, hlam, p2380_1]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h1559, hlam, p2380_0]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [h1560, hlam, p2380_1]
              · have p2380_0 := h2380c.1
                have p2380_1 := h2380c.2.1
                have p2380_2 := h2380c.2.2.1
                have p2380_3 := h2380c.2.2.2
                linarith only [hlam, p2380_0]
            · linarith only [h1561, h1565, h1566, h2377, h2379, hc35, hlam, hphi, u5elo4]
          · linarith only [h1385, h2375, h2378, h3, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
        · linarith only [h1558, h1561, h1566, h2377, h4, hc12, hc35, hlam, hphi, ht23]
      · linarith only [h1558, h2376, h4, hlam]
    · linarith only [h2375, hc14, hlam, hphi, ht45, u5elo4]
  · linarith only [h1561, h1565, h2374, hc25, hlam, hphi, u5elo3]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 3 4 (by decide) (by decide) with h1566 | h1566
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565 h1566

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h1565, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 5 (by decide) (by decide) with h1565 | h1565
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563 h1565

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 4 (by decide) (by decide) with h1563 | h1563
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561 h1563

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h1561 | h1561
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560 h1561

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h1560, hc04, hlam, hphi, ht45, u5elo4]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h1560 | h1560
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559 h1560

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h1559, hc03, hlam, hphi, ht34, ht45, u5elo3]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h1559 | h1559
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1385 h1557 h1558 h1559

end R2N4
