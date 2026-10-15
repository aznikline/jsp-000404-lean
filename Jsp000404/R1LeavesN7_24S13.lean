import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_24S11
import Jsp000404.R1LeavesN7_24S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1160 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1498 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1640 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h2389 | h2389
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2390 | h2390
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2391 | h2391
      · linarith only [h0, h2389, h2391, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2393 | h2393
        · linarith only [h0, h1160, h2393, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2395 | h2395
          · linarith only [h1640, h2389, h2395, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2397 | h2397
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2398 | h2398
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2399 | h2399
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2400 | h2400
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2401 | h2401
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2402 | h2402
                      · rcases h0bigk with h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c | h2403c
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [hlam, p2403_0]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          rcases p2403_3 (m.d 0 1) (by simp) with h2405 | h2405
                          · rcases p2403_3 (m.d 0 2) (by simp) with h2406 | h2406
                            · linarith only [h0, h2406, hlam]
                            · rcases p2403_3 (m.d 0 3) (by simp) with h2408 | h2408
                              · linarith only [h1, h2408, hlam]
                              · linarith only [h2408, h4, hlam]
                          · linarith only [h0, h2405, hlam]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h1, h2397, h2402, hc45, hlam, hphi, ht01, ht0b, ht5b, p2403_1, u1elo0]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h1, h1640, h2397, h2402, hc45, hlam, hphi, ht01, ht0b, ht5b, p2403_1, u1elo0]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          rcases p2403_3 (m.d 0 1) (by simp) with h2414 | h2414
                          · rcases p2403_3 (m.d 0 2) (by simp) with h2415 | h2415
                            · linarith only [h0, h2415, hlam]
                            · rcases p2403_3 (m.d 0 3) (by simp) with h2417 | h2417
                              · linarith only [h1, h2417, hlam]
                              · linarith only [h2389, h2417, hlam]
                          · linarith only [h2414, h3, hlam]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h0, hlam, p2403_0]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [hlam, p2403_0]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h4, hlam, p2403_0]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h1160, hlam, p2403_1]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h1498, hlam, p2403_0]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h1, hlam, p2403_1]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h0, h1640, h2399, hc12, hc23, hlam, hphi, p2403_1]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [hlam, p2403_0]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h1640, hlam, p2403_1]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h1640, h2399, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2403_1]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h2, hlam, p2403_0]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h0, h1640, h2399, hc12, hc23, hlam, hphi, p2403_1]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h1, h1640, h2397, h2399, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2403_1]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [hlam, p2403_0]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h0, h1498, h1640, h2399, hc12, hc23, hlam, hphi, p2403_1]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h3, hlam, p2403_0]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h0, h1640, h2389, h2399, hc12, hc23, hlam, hphi, p2403_1]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h2389, hlam, p2403_0]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [h2390, hlam, p2403_1]
                        · have p2403_0 := h2403c.1
                          have p2403_1 := h2403c.2.1
                          have p2403_2 := h2403c.2.2.1
                          have p2403_3 := h2403c.2.2.2
                          linarith only [hlam, p2403_0]
                      · linarith only [h1640, h2, h2390, h2402, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h1640, h2, h2398, h2399, h2401, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h1640, h2397, h2400, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2444 | h2444
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2445 | h2445
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2446 | h2446
                      · rcases h0bigk with h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c | h2447c
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [hlam, p2447_0]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          rcases p2447_3 (m.d 0 1) (by simp) with h2449 | h2449
                          · rcases p2447_3 (m.d 0 2) (by simp) with h2450 | h2450
                            · linarith only [h0, h2450, hlam]
                            · rcases p2447_3 (m.d 0 3) (by simp) with h2452 | h2452
                              · linarith only [h1, h2452, hlam]
                              · linarith only [h2452, h4, hlam]
                          · linarith only [h0, h2449, hlam]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h1, h2397, hc35, hlam, hphi, ht01, ht0b, ht5b, p2447_1, u1elo0]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h1, h1640, h2397, hc35, hlam, hphi, ht01, ht0b, ht5b, p2447_1, u1elo0]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          rcases p2447_3 (m.d 0 1) (by simp) with h2458 | h2458
                          · rcases p2447_3 (m.d 0 2) (by simp) with h2459 | h2459
                            · linarith only [h0, h2459, hlam]
                            · rcases p2447_3 (m.d 0 3) (by simp) with h2461 | h2461
                              · linarith only [h1, h2461, hlam]
                              · linarith only [h2389, h2461, hlam]
                          · linarith only [h2458, h3, hlam]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h0, hlam, p2447_0]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [hlam, p2447_0]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h4, hlam, p2447_0]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h1160, hlam, p2447_1]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h1498, hlam, p2447_0]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h1, hlam, p2447_1]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h0, h2399, h4, hc12, hc34, hlam, hphi, ht23, p2447_1]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [hlam, p2447_0]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h1640, hlam, p2447_1]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h0, h1498, h2399, h4, hc12, hc34, hlam, hphi, ht23, p2447_1]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h2, hlam, p2447_0]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          rcases p2447_3 (m.d 0 1) (by simp) with h2476 | h2476
                          · rcases p2447_3 (m.d 0 2) (by simp) with h2477 | h2477
                            · linarith only [h1160, h2477, hlam]
                            · rcases p2447_3 (m.d 0 3) (by simp) with h2479 | h2479
                              · linarith only [h1640, h2479, hlam]
                              · linarith only [h2479, h4, hlam]
                          · linarith only [h0, h2476, hlam]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h1, h2397, hc35, hlam, hphi, ht0b, ht5b, p2447_1, u0elo3]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [hlam, p2447_0]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          rcases p2447_3 (m.d 0 1) (by simp) with h2485 | h2485
                          · rcases p2447_3 (m.d 0 2) (by simp) with h2486 | h2486
                            · linarith only [h1160, h2486, hlam]
                            · rcases p2447_3 (m.d 0 3) (by simp) with h2488 | h2488
                              · linarith only [h1640, h2488, hlam]
                              · linarith only [h2389, h2488, hlam]
                          · linarith only [h2485, h3, hlam]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h3, hlam, p2447_0]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h0, h2389, h2399, h4, hc12, hc34, hlam, hphi, ht23, p2447_1]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h2389, hlam, p2447_0]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [h2390, hlam, p2447_1]
                        · have p2447_0 := h2447c.1
                          have p2447_1 := h2447c.2.1
                          have p2447_2 := h2447c.2.2.1
                          have p2447_3 := h2447c.2.2.2
                          linarith only [hlam, p2447_0]
                      · linarith only [h0, h2399, h2446, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h1160, h2, h2398, h2445, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h2397, h2444, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h2390, h2395, h2397, h2398, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
            · linarith only [h1640, h2389, h2397, hc13, hc34, hlam, hphi]
    · linarith only [h1640, h2389, h2390, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2503 | h2503
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2504 | h2504
      · linarith only [h0, h2504, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2506 | h2506
        · linarith only [h1, h1160, h2389, h2503, h2504, h2506, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2508 | h2508
          · linarith only [h1, h1640, h2508, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2510 | h2510
            · linarith only [h1, h2389, h2510, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2512 | h2512
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2513 | h2513
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2514 | h2514
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2515 | h2515
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2516 | h2516
                      · rcases h0bigk with h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c | h2517c
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [hlam, p2517_0]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          rcases p2517_3 (m.d 0 1) (by simp) with h2519 | h2519
                          · rcases p2517_3 (m.d 0 2) (by simp) with h2520 | h2520
                            · linarith only [h0, h2520, hlam]
                            · rcases p2517_3 (m.d 0 3) (by simp) with h2522 | h2522
                              · linarith only [h1, h2522, hlam]
                              · linarith only [h2522, h4, hlam]
                          · linarith only [h0, h2519, hlam]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          rcases p2517_3 (m.d 0 1) (by simp) with h2526 | h2526
                          · rcases p2517_3 (m.d 0 2) (by simp) with h2527 | h2527
                            · linarith only [h0, h2527, hlam]
                            · rcases p2517_3 (m.d 0 3) (by simp) with h2529 | h2529
                              · linarith only [h1, h2529, hlam]
                              · rcases p2517_3 (m.d 0 4) (by simp) with h2531 | h2531
                                · linarith only [h2, h2531, hlam]
                                · linarith only [h1640, h2531, hlam]
                          · linarith only [h1, h2526, hlam]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h2, h2512, hc45, hlam, hphi, ht01, ht0b, ht5b, p2517_1, u1elo0]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          rcases p2517_3 (m.d 0 1) (by simp) with h2536 | h2536
                          · rcases p2517_3 (m.d 0 2) (by simp) with h2537 | h2537
                            · linarith only [h0, h2537, hlam]
                            · rcases p2517_3 (m.d 0 3) (by simp) with h2539 | h2539
                              · linarith only [h1, h2539, hlam]
                              · rcases p2517_3 (m.d 0 4) (by simp) with h2541 | h2541
                                · linarith only [h2, h2541, hlam]
                                · linarith only [h2503, h2541, hlam]
                          · linarith only [h2536, h3, hlam]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h0, hlam, p2517_0]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [hlam, p2517_0]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h4, hlam, p2517_0]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h1160, hlam, p2517_1]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h1498, hlam, p2517_0]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h1, hlam, p2517_1]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h0, h2389, h2513, h2516, hc12, hc23, hlam, hphi, p2517_1]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [hlam, p2517_0]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h1640, hlam, p2517_1]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h2389, hlam, p2517_1]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h2, hlam, p2517_0]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h0, h1640, h2513, hc12, hc23, hlam, hphi, p2517_1]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h0, h1640, h2513, h4, hc12, hc23, hlam, hphi, p2517_1]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [hlam, p2517_0]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h0, h1640, h2389, h2513, h4, hc12, hc23, hlam, hphi, p2517_1]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h3, hlam, p2517_0]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h0, h2389, h2513, h2516, hc12, hc23, hlam, hphi, p2517_1]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h0, h2389, h2513, h2516, h4, hc12, hc23, hlam, hphi, p2517_1]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [h2503, hlam, p2517_1]
                        · have p2517_0 := h2517c.1
                          have p2517_1 := h2517c.2.1
                          have p2517_2 := h2517c.2.2.1
                          have p2517_3 := h2517c.2.2.2
                          linarith only [hlam, p2517_0]
                      · linarith only [h1640, h2, h2512, h2516, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1640, h2, h2512, h2513, h2515, hlam]
                  · linarith only [h0, h1640, h2513, h2514, h4, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2568 | h2568
                  · linarith only [h0, h2389, h2513, h2568, h4, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2570 | h2570
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2571 | h2571
                      · rcases h0bigk with h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c | h2572c
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [hlam, p2572_0]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          rcases p2572_3 (m.d 0 1) (by simp) with h2574 | h2574
                          · rcases p2572_3 (m.d 0 2) (by simp) with h2575 | h2575
                            · linarith only [h0, h2575, hlam]
                            · rcases p2572_3 (m.d 0 3) (by simp) with h2577 | h2577
                              · linarith only [h1, h2577, hlam]
                              · linarith only [h2577, h4, hlam]
                          · linarith only [h0, h2574, hlam]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          rcases p2572_3 (m.d 0 1) (by simp) with h2581 | h2581
                          · rcases p2572_3 (m.d 0 2) (by simp) with h2582 | h2582
                            · linarith only [h0, h2582, hlam]
                            · rcases p2572_3 (m.d 0 3) (by simp) with h2584 | h2584
                              · linarith only [h1, h2584, hlam]
                              · rcases p2572_3 (m.d 0 4) (by simp) with h2586 | h2586
                                · linarith only [h2, h2586, hlam]
                                · linarith only [h1640, h2586, hlam]
                          · linarith only [h1, h2581, hlam]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [h2, h2512, hc45, hlam, hphi, ht01, ht0b, ht5b, p2572_1, u1elo0]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          rcases p2572_3 (m.d 0 1) (by simp) with h2591 | h2591
                          · rcases p2572_3 (m.d 0 2) (by simp) with h2592 | h2592
                            · linarith only [h0, h2592, hlam]
                            · rcases p2572_3 (m.d 0 3) (by simp) with h2594 | h2594
                              · linarith only [h1, h2594, hlam]
                              · rcases p2572_3 (m.d 0 4) (by simp) with h2596 | h2596
                                · linarith only [h2, h2596, hlam]
                                · linarith only [h2503, h2596, hlam]
                          · linarith only [h2591, h3, hlam]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [h0, hlam, p2572_0]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [hlam, p2572_0]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [h4, hlam, p2572_0]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [h1160, hlam, p2572_1]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [h1498, hlam, p2572_0]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [h1, hlam, p2572_1]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [h0, h2568, h2571, h4, hc12, hc34, hlam, hphi, ht23, p2572_1]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [hlam, p2572_0]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [h1640, hlam, p2572_1]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [h2389, hlam, p2572_1]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [h2, hlam, p2572_0]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          rcases p2572_3 (m.d 0 1) (by simp) with h2611 | h2611
                          · rcases p2572_3 (m.d 0 2) (by simp) with h2612 | h2612
                            · linarith only [h1160, h2612, hlam]
                            · rcases p2572_3 (m.d 0 3) (by simp) with h2614 | h2614
                              · linarith only [h1640, h2614, hlam]
                              · linarith only [h2614, h4, hlam]
                          · linarith only [h0, h2611, hlam]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          rcases p2572_3 (m.d 0 1) (by simp) with h2618 | h2618
                          · rcases p2572_3 (m.d 0 2) (by simp) with h2619 | h2619
                            · linarith only [h1160, h2619, hlam]
                            · rcases p2572_3 (m.d 0 3) (by simp) with h2621 | h2621
                              · linarith only [h1640, h2621, hlam]
                              · rcases p2572_3 (m.d 0 4) (by simp) with h2623 | h2623
                                · rcases p2572_3 (m.d 0 5) (by simp) with h2624 | h2624
                                  · linarith only [h2503, h2624, hlam]
                                  · linarith only [h2389, h2624, hlam]
                                · linarith only [h1640, h2623, hlam]
                          · linarith only [h1, h2618, hlam]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [hlam, p2572_0]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          rcases p2572_3 (m.d 0 1) (by simp) with h2630 | h2630
                          · rcases p2572_3 (m.d 0 2) (by simp) with h2631 | h2631
                            · linarith only [h1160, h2631, hlam]
                            · rcases p2572_3 (m.d 0 3) (by simp) with h2633 | h2633
                              · linarith only [h1640, h2633, hlam]
                              · rcases p2572_3 (m.d 0 4) (by simp) with h2635 | h2635
                                · rcases p2572_3 (m.d 0 5) (by simp) with h2636 | h2636
                                  · linarith only [h2503, h2636, hlam]
                                  · rcases h3bigk with h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c | h2638c
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [hlam, p2638_0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h2, h2389, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2572_1, p2638_1, u1elo0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h4, hlam, p2638_1]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h1640, hlam, p2638_0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h2389, hlam, p2638_0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h1, hlam, p2638_0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [hlam, p2638_0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h2504, hlam, p2638_1]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h2508, hlam, p2638_0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h2510, hlam, p2638_0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h2568, h2571, hc03, hc34, hlam, hphi, p2638_1]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h2568, h2571, hc13, hc34, hlam, hphi, p2638_1]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [hlam, p2638_0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h2513, hlam, p2638_0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h2568, hlam, p2638_0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      rcases p2638_3 (m.d 0 3) (by simp) with h2654 | h2654
                                      · linarith only [h2654, hlam, p2638_0]
                                      · rcases p2638_3 (m.d 1 3) (by simp) with h2656 | h2656
                                        · linarith only [h2508, h2656, hlam]
                                        · rcases p2638_3 (m.d 2 3) (by simp) with h2658 | h2658
                                          · linarith only [h2513, h2658, hlam]
                                          · linarith only [h2658, h4, hlam]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      rcases p2638_3 (m.d 0 3) (by simp) with h2661 | h2661
                                      · linarith only [h1640, h2661, hlam]
                                      · linarith only [h1, h2661, hlam]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p2638_1]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [hlam, p2638_0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h0, h2389, h4, hc12, hc34, hlam, hphi, ht23, p2638_1]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      rcases p2638_3 (m.d 0 3) (by simp) with h2667 | h2667
                                      · linarith only [h2667, hlam, p2638_0]
                                      · rcases p2638_3 (m.d 1 3) (by simp) with h2669 | h2669
                                        · linarith only [h2510, h2669, hlam]
                                        · rcases p2638_3 (m.d 2 3) (by simp) with h2671 | h2671
                                          · linarith only [h2568, h2671, hlam]
                                          · linarith only [h2671, h4, hlam]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      rcases p2638_3 (m.d 0 3) (by simp) with h2674 | h2674
                                      · linarith only [h2389, h2674, hlam]
                                      · linarith only [h1, h2674, hlam]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p2638_1]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [h2571, hlam, p2638_0]
                                    · have p2638_0 := h2638c.1
                                      have p2638_1 := h2638c.2.1
                                      have p2638_2 := h2638c.2.2.1
                                      have p2638_3 := h2638c.2.2.2
                                      linarith only [hlam, p2638_0]
                                · linarith only [h2503, h2635, hlam]
                          · linarith only [h2630, h3, hlam]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [h3, hlam, p2572_0]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          rcases p2572_3 (m.d 0 1) (by simp) with h2683 | h2683
                          · rcases p2572_3 (m.d 0 2) (by simp) with h2684 | h2684
                            · linarith only [h1498, h2684, hlam]
                            · rcases p2572_3 (m.d 0 3) (by simp) with h2686 | h2686
                              · linarith only [h2389, h2686, hlam]
                              · linarith only [h2686, h4, hlam]
                          · linarith only [h0, h2683, hlam]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          rcases p2572_3 (m.d 0 1) (by simp) with h2690 | h2690
                          · rcases p2572_3 (m.d 0 2) (by simp) with h2691 | h2691
                            · linarith only [h1498, h2691, hlam]
                            · rcases p2572_3 (m.d 0 3) (by simp) with h2693 | h2693
                              · linarith only [h2389, h2693, hlam]
                              · rcases p2572_3 (m.d 0 4) (by simp) with h2695 | h2695
                                · rcases p2572_3 (m.d 0 5) (by simp) with h2696 | h2696
                                  · rcases h3bigk with h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c | h2697c
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [hlam, p2697_0]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h2504, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2572_1, p2697_1, u0elo4]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h4, hlam, p2697_1]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h1640, hlam, p2697_0]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h2389, hlam, p2697_0]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h1, hlam, p2697_0]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [hlam, p2697_0]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h2504, hlam, p2697_1]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h2508, hlam, p2697_0]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h2510, hlam, p2697_0]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h1, h2504, h2513, hc12, hc34, hlam, hphi, ht23, p2697_1]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h2504, h2513, hc12, hc34, hlam, hphi, ht23, p2697_1]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [hlam, p2697_0]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h2513, hlam, p2697_0]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h2568, hlam, p2697_0]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      rcases p2697_3 (m.d 0 3) (by simp) with h2713 | h2713
                                      · linarith only [h2713, hlam, p2697_0]
                                      · rcases p2697_3 (m.d 1 3) (by simp) with h2715 | h2715
                                        · linarith only [h2508, h2715, hlam]
                                        · rcases p2697_3 (m.d 2 3) (by simp) with h2717 | h2717
                                          · linarith only [h2513, h2717, hlam]
                                          · linarith only [h2717, h4, hlam]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      rcases p2697_3 (m.d 0 3) (by simp) with h2720 | h2720
                                      · linarith only [h1640, h2720, hlam]
                                      · linarith only [h1, h2720, hlam]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p2697_1]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [hlam, p2697_0]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h1, h2389, h2504, hc12, hc34, hlam, hphi, ht23, p2697_1]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      rcases p2697_3 (m.d 0 3) (by simp) with h2726 | h2726
                                      · linarith only [h2726, hlam, p2697_0]
                                      · rcases p2697_3 (m.d 1 3) (by simp) with h2728 | h2728
                                        · linarith only [h2510, h2728, hlam]
                                        · rcases p2697_3 (m.d 2 3) (by simp) with h2730 | h2730
                                          · linarith only [h2568, h2730, hlam]
                                          · linarith only [h2730, h4, hlam]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      rcases p2697_3 (m.d 0 3) (by simp) with h2733 | h2733
                                      · linarith only [h2389, h2733, hlam]
                                      · linarith only [h1, h2733, hlam]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p2697_1]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [h2571, hlam, p2697_0]
                                    · have p2697_0 := h2697c.1
                                      have p2697_1 := h2697c.2.1
                                      have p2697_2 := h2697c.2.2.1
                                      have p2697_3 := h2697c.2.2.2
                                      linarith only [hlam, p2697_0]
                                  · linarith only [h2389, h2696, hlam]
                                · linarith only [h1640, h2695, hlam]
                          · linarith only [h1, h2690, hlam]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [h2503, hlam, p2572_1]
                        · have p2572_0 := h2572c.1
                          have p2572_1 := h2572c.2.1
                          have p2572_2 := h2572c.2.2.1
                          have p2572_3 := h2572c.2.2.2
                          linarith only [hlam, p2572_0]
                      · linarith only [h2, h2512, h2513, h2571, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1160, h2, h2512, h2570, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2746 | h2746
                · linarith only [h1640, h2503, h2504, h2508, h2512, h2746, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2748 | h2748
                  · linarith only [h1, h2389, h2504, h2746, h2748, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2750 | h2750
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2751 | h2751
                      · rcases h0bigk with h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c | h2752c
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [hlam, p2752_0]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          rcases p2752_3 (m.d 0 1) (by simp) with h2754 | h2754
                          · rcases p2752_3 (m.d 0 2) (by simp) with h2755 | h2755
                            · linarith only [h0, h2755, hlam]
                            · rcases p2752_3 (m.d 0 3) (by simp) with h2757 | h2757
                              · linarith only [h1, h2757, hlam]
                              · linarith only [h2757, h4, hlam]
                          · linarith only [h0, h2754, hlam]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          rcases p2752_3 (m.d 0 1) (by simp) with h2761 | h2761
                          · rcases p2752_3 (m.d 0 2) (by simp) with h2762 | h2762
                            · linarith only [h0, h2762, hlam]
                            · rcases p2752_3 (m.d 0 3) (by simp) with h2764 | h2764
                              · linarith only [h1, h2764, hlam]
                              · rcases p2752_3 (m.d 0 4) (by simp) with h2766 | h2766
                                · linarith only [h2, h2766, hlam]
                                · linarith only [h1640, h2766, hlam]
                          · linarith only [h1, h2761, hlam]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h2503, h2504, h2508, h2512, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2752_1, u1elo0]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h2503, h2504, h2508, h2512, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2752_1, u1elo0]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h0, hlam, p2752_0]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [hlam, p2752_0]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h4, hlam, p2752_0]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h1160, hlam, p2752_1]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h1498, hlam, p2752_0]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h1, hlam, p2752_1]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h0, h2748, h2751, h4, hc12, hc34, hlam, hphi, ht23, p2752_1]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [hlam, p2752_0]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h1640, hlam, p2752_1]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h2389, hlam, p2752_1]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h2, hlam, p2752_0]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          rcases p2752_3 (m.d 0 1) (by simp) with h2783 | h2783
                          · rcases p2752_3 (m.d 0 2) (by simp) with h2784 | h2784
                            · linarith only [h1160, h2784, hlam]
                            · rcases p2752_3 (m.d 0 3) (by simp) with h2786 | h2786
                              · linarith only [h1640, h2786, hlam]
                              · linarith only [h2786, h4, hlam]
                          · linarith only [h0, h2783, hlam]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          rcases p2752_3 (m.d 0 1) (by simp) with h2790 | h2790
                          · rcases p2752_3 (m.d 0 2) (by simp) with h2791 | h2791
                            · linarith only [h1160, h2791, hlam]
                            · rcases p2752_3 (m.d 0 3) (by simp) with h2793 | h2793
                              · linarith only [h1640, h2793, hlam]
                              · rcases p2752_3 (m.d 0 4) (by simp) with h2795 | h2795
                                · rcases p2752_3 (m.d 0 5) (by simp) with h2796 | h2796
                                  · linarith only [h2503, h2796, hlam]
                                  · linarith only [h2389, h2796, hlam]
                                · linarith only [h1640, h2795, hlam]
                          · linarith only [h1, h2790, hlam]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [hlam, p2752_0]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h2503, h2504, h2508, h2512, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2752_1, u0elo3]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h3, hlam, p2752_0]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          rcases p2752_3 (m.d 0 1) (by simp) with h2804 | h2804
                          · rcases p2752_3 (m.d 0 2) (by simp) with h2805 | h2805
                            · linarith only [h1498, h2805, hlam]
                            · rcases p2752_3 (m.d 0 3) (by simp) with h2807 | h2807
                              · linarith only [h2389, h2807, hlam]
                              · linarith only [h2807, h4, hlam]
                          · linarith only [h0, h2804, hlam]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          rcases p2752_3 (m.d 0 1) (by simp) with h2811 | h2811
                          · rcases p2752_3 (m.d 0 2) (by simp) with h2812 | h2812
                            · linarith only [h1498, h2812, hlam]
                            · rcases p2752_3 (m.d 0 3) (by simp) with h2814 | h2814
                              · linarith only [h2389, h2814, hlam]
                              · rcases p2752_3 (m.d 0 4) (by simp) with h2816 | h2816
                                · rcases p2752_3 (m.d 0 5) (by simp) with h2817 | h2817
                                  · rcases h3bigk with h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c | h2818c
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [hlam, p2818_0]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h2504, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2752_1, p2818_1, u0elo4]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h4, hlam, p2818_1]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h1640, hlam, p2818_0]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h2389, hlam, p2818_0]
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
                                      linarith only [h2504, hlam, p2818_1]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h2508, hlam, p2818_0]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h2510, hlam, p2818_0]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h2748, h2751, hc03, hc34, hlam, hphi, p2818_1]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h2504, h2748, h2751, hc12, hc34, hlam, hphi, ht23, p2818_1]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [hlam, p2818_0]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h2746, hlam, p2818_0]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h2748, hlam, p2818_0]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      rcases p2818_3 (m.d 0 3) (by simp) with h2834 | h2834
                                      · linarith only [h2834, hlam, p2818_0]
                                      · rcases p2818_3 (m.d 1 3) (by simp) with h2836 | h2836
                                        · linarith only [h2508, h2836, hlam]
                                        · rcases p2818_3 (m.d 2 3) (by simp) with h2838 | h2838
                                          · linarith only [h2746, h2838, hlam]
                                          · linarith only [h2838, h4, hlam]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      rcases p2818_3 (m.d 0 3) (by simp) with h2841 | h2841
                                      · linarith only [h1640, h2841, hlam]
                                      · linarith only [h1, h2841, hlam]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p2818_1]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [hlam, p2818_0]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h1, h2389, h2504, hc12, hc34, hlam, hphi, ht23, p2818_1]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      rcases p2818_3 (m.d 0 3) (by simp) with h2847 | h2847
                                      · linarith only [h2847, hlam, p2818_0]
                                      · rcases p2818_3 (m.d 1 3) (by simp) with h2849 | h2849
                                        · linarith only [h2510, h2849, hlam]
                                        · rcases p2818_3 (m.d 2 3) (by simp) with h2851 | h2851
                                          · linarith only [h2748, h2851, hlam]
                                          · linarith only [h2851, h4, hlam]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      rcases p2818_3 (m.d 0 3) (by simp) with h2854 | h2854
                                      · linarith only [h2389, h2854, hlam]
                                      · linarith only [h1, h2854, hlam]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p2818_1]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [h2751, hlam, p2818_0]
                                    · have p2818_0 := h2818c.1
                                      have p2818_1 := h2818c.2.1
                                      have p2818_2 := h2818c.2.2.1
                                      have p2818_3 := h2818c.2.2.2
                                      linarith only [hlam, p2818_0]
                                  · linarith only [h2389, h2817, hlam]
                                · linarith only [h1640, h2816, hlam]
                          · linarith only [h1, h2811, hlam]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [h2503, hlam, p2752_1]
                        · have p2752_0 := h2752c.1
                          have p2752_1 := h2752c.2.1
                          have p2752_2 := h2752c.2.2.1
                          have p2752_3 := h2752c.2.2.2
                          linarith only [hlam, p2752_0]
                      · linarith only [h1640, h2503, h2751, hlam]
                    · linarith only [h1160, h2503, h2750, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2867 | h2867
      · linarith only [h0, h2867, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2869 | h2869
        · linarith only [h0, h1160, h2869, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2871 | h2871
          · linarith only [h0, h1, h1640, h2871, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2873 | h2873
            · linarith only [h1, h2389, h2873, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2875 | h2875
              · linarith only [h1640, h2, h2503, h2875, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2877 | h2877
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2878 | h2878
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2879 | h2879
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2880 | h2880
                      · linarith only [h0, h1640, h2503, h2877, h2880, h4, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1640, h2877, h2879, h2880, h4, hc12, hc23, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2883 | h2883
                      · linarith only [h0, h1160, h2879, h2883, hc12, hc34, hlam, hphi, ht23]
                      · rcases h0bigk with h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c | h2885c
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [hlam, p2885_0]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          rcases p2885_3 (m.d 0 1) (by simp) with h2887 | h2887
                          · rcases p2885_3 (m.d 0 2) (by simp) with h2888 | h2888
                            · linarith only [h0, h2888, hlam]
                            · rcases p2885_3 (m.d 0 3) (by simp) with h2890 | h2890
                              · linarith only [h1, h2890, hlam]
                              · linarith only [h2890, h4, hlam]
                          · linarith only [h0, h2887, hlam]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          rcases p2885_3 (m.d 0 1) (by simp) with h2894 | h2894
                          · rcases p2885_3 (m.d 0 2) (by simp) with h2895 | h2895
                            · linarith only [h0, h2895, hlam]
                            · rcases p2885_3 (m.d 0 3) (by simp) with h2897 | h2897
                              · linarith only [h1, h2897, hlam]
                              · rcases p2885_3 (m.d 0 4) (by simp) with h2899 | h2899
                                · linarith only [h2, h2899, hlam]
                                · linarith only [h1640, h2899, hlam]
                          · linarith only [h1, h2894, hlam]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          rcases p2885_3 (m.d 0 1) (by simp) with h2903 | h2903
                          · rcases p2885_3 (m.d 0 2) (by simp) with h2904 | h2904
                            · linarith only [h0, h2904, hlam]
                            · rcases p2885_3 (m.d 0 3) (by simp) with h2906 | h2906
                              · linarith only [h1, h2906, hlam]
                              · rcases p2885_3 (m.d 0 4) (by simp) with h2908 | h2908
                                · linarith only [h2, h2908, hlam]
                                · rcases p2885_3 (m.d 0 5) (by simp) with h2910 | h2910
                                  · linarith only [h2910, h3, hlam]
                                  · linarith only [h2503, h2910, hlam]
                          · linarith only [h2, h2903, hlam]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          rcases p2885_3 (m.d 0 1) (by simp) with h2914 | h2914
                          · rcases p2885_3 (m.d 0 2) (by simp) with h2915 | h2915
                            · linarith only [h0, h2915, hlam]
                            · rcases p2885_3 (m.d 0 3) (by simp) with h2917 | h2917
                              · linarith only [h1, h2917, hlam]
                              · rcases p2885_3 (m.d 0 4) (by simp) with h2919 | h2919
                                · linarith only [h2, h2919, hlam]
                                · rcases p2885_3 (m.d 0 5) (by simp) with h2921 | h2921
                                  · linarith only [h2921, h3, hlam]
                                  · rcases h3bigk with h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h1640, hc13, hc34, hlam, hphi, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h4, hlam, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h1640, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2389, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h1, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2867, hlam, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2871, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2873, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      rcases p2923_3 (m.d 0 3) (by simp) with h2934 | h2934
                                      · linarith only [h2934, h4, hlam]
                                      · rcases p2923_3 (m.d 1 3) (by simp) with h2936 | h2936
                                        · linarith only [h2867, h2936, hlam]
                                        · rcases p2923_3 (m.d 2 3) (by simp) with h2938 | h2938
                                          · rcases p2923_3 (m.d 3 4) (by simp) with h2939 | h2939
                                            · linarith only [h2877, h2939, hlam]
                                            · linarith only [h1640, h2939, hlam]
                                          · linarith only [h2938, h4, hlam]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      rcases p2923_3 (m.d 0 3) (by simp) with h2943 | h2943
                                      · linarith only [h2943, h4, hlam]
                                      · linarith only [h1, h2943, hlam]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h0, h1640, h4, hc12, hc23, hlam, hphi, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h0, h2389, h4, hc12, hc23, hlam, hphi, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h0, h2877, h4, hc12, hc23, hlam, hphi, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2867, h2877, hc12, hc23, hlam, hphi, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2877, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2883, hlam, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h0, h2878, h4, hc12, hc23, hlam, hphi, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2867, h2878, hc12, hc23, hlam, hphi, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2878, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h0, h1640, h2878, h4, hc12, hc23, hlam, hphi, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hlam, p2923_0]
                          · linarith only [h2914, h3, hlam]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h0, hlam, p2885_0]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [hlam, p2885_0]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h4, hlam, p2885_0]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h1160, hlam, p2885_1]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h1498, hlam, p2885_0]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h1, hlam, p2885_1]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h0, h1160, h1640, h2879, hc12, hc45, hlam, hphi, ht23, ht34, p2885_1]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [hlam, p2885_0]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h1640, hlam, p2885_1]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h2389, hlam, p2885_1]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h2, hlam, p2885_0]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h0, h1160, h2879, hc12, hc45, hlam, hphi, ht23, ht34, p2885_1]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h1160, h2879, hc03, hc45, hlam, hphi, ht34, p2885_1]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [hlam, p2885_0]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h2503, hlam, p2885_0]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h3, hlam, p2885_0]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h0, h2389, h2878, hc12, hc23, hlam, hphi, p2885_1]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h1, h2389, h2867, h2878, hc12, hc23, hlam, hphi, p2885_1]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [h0, h1160, h2389, h2878, hc12, hc23, hlam, hphi, p2885_1]
                        · have p2885_0 := h2885c.1
                          have p2885_1 := h2885c.2.1
                          have p2885_2 := h2885c.2.2.1
                          have p2885_3 := h2885c.2.2.2
                          linarith only [hlam, p2885_0]
                  · linarith only [h0, h1640, h2877, h2878, h4, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2981 | h2981
                  · linarith only [h0, h2389, h2877, h2981, h4, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2983 | h2983
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2984 | h2984
                      · rcases h0bigk with h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c | h2985c
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [hlam, p2985_0]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          rcases p2985_3 (m.d 0 1) (by simp) with h2987 | h2987
                          · rcases p2985_3 (m.d 0 2) (by simp) with h2988 | h2988
                            · linarith only [h0, h2988, hlam]
                            · rcases p2985_3 (m.d 0 3) (by simp) with h2990 | h2990
                              · linarith only [h1, h2990, hlam]
                              · linarith only [h2990, h4, hlam]
                          · linarith only [h0, h2987, hlam]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          rcases p2985_3 (m.d 0 1) (by simp) with h2994 | h2994
                          · rcases p2985_3 (m.d 0 2) (by simp) with h2995 | h2995
                            · linarith only [h0, h2995, hlam]
                            · rcases p2985_3 (m.d 0 3) (by simp) with h2997 | h2997
                              · linarith only [h1, h2997, hlam]
                              · rcases p2985_3 (m.d 0 4) (by simp) with h2999 | h2999
                                · linarith only [h2, h2999, hlam]
                                · linarith only [h1640, h2999, hlam]
                          · linarith only [h1, h2994, hlam]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          rcases p2985_3 (m.d 0 1) (by simp) with h3003 | h3003
                          · rcases p2985_3 (m.d 0 2) (by simp) with h3004 | h3004
                            · linarith only [h0, h3004, hlam]
                            · rcases p2985_3 (m.d 0 3) (by simp) with h3006 | h3006
                              · linarith only [h1, h3006, hlam]
                              · rcases p2985_3 (m.d 0 4) (by simp) with h3008 | h3008
                                · linarith only [h2, h3008, hlam]
                                · rcases p2985_3 (m.d 0 5) (by simp) with h3010 | h3010
                                  · linarith only [h3, h3010, hlam]
                                  · linarith only [h2503, h3010, hlam]
                          · linarith only [h2, h3003, hlam]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          rcases p2985_3 (m.d 0 1) (by simp) with h3014 | h3014
                          · rcases p2985_3 (m.d 0 2) (by simp) with h3015 | h3015
                            · linarith only [h0, h3015, hlam]
                            · rcases p2985_3 (m.d 0 3) (by simp) with h3017 | h3017
                              · linarith only [h1, h3017, hlam]
                              · rcases p2985_3 (m.d 0 4) (by simp) with h3019 | h3019
                                · linarith only [h2, h3019, hlam]
                                · rcases p2985_3 (m.d 0 5) (by simp) with h3021 | h3021
                                  · linarith only [h3, h3021, hlam]
                                  · rcases h3bigk with h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c | h3023c
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [hlam, p3023_0]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h2981, h2984, h4, hc13, hc34, hlam, hphi, p3023_1]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h4, hlam, p3023_1]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h1640, hlam, p3023_0]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h2389, hlam, p3023_0]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h1, hlam, p3023_0]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [hlam, p3023_0]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h2867, hlam, p3023_1]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h2871, hlam, p3023_0]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h2873, hlam, p3023_0]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h2981, h2984, hc03, hc34, hlam, hphi, p3023_1]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h2981, h2984, hc13, hc34, hlam, hphi, p3023_1]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [hlam, p3023_0]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h2877, hlam, p3023_0]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h2981, hlam, p3023_0]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      rcases p3023_3 (m.d 0 3) (by simp) with h3039 | h3039
                                      · linarith only [h3039, hlam, p3023_0]
                                      · rcases p3023_3 (m.d 1 3) (by simp) with h3041 | h3041
                                        · linarith only [h2871, h3041, hlam]
                                        · rcases p3023_3 (m.d 2 3) (by simp) with h3043 | h3043
                                          · linarith only [h2877, h3043, hlam]
                                          · linarith only [h3043, h4, hlam]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      rcases p3023_3 (m.d 0 3) (by simp) with h3046 | h3046
                                      · linarith only [h1640, h3046, hlam]
                                      · linarith only [h1, h3046, hlam]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p3023_1]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [hlam, p3023_0]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h0, h2389, h4, hc12, hc34, hlam, hphi, ht23, p3023_1]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      rcases p3023_3 (m.d 0 3) (by simp) with h3052 | h3052
                                      · linarith only [h3052, hlam, p3023_0]
                                      · rcases p3023_3 (m.d 1 3) (by simp) with h3054 | h3054
                                        · linarith only [h2873, h3054, hlam]
                                        · rcases p3023_3 (m.d 2 3) (by simp) with h3056 | h3056
                                          · linarith only [h2981, h3056, hlam]
                                          · linarith only [h3056, h4, hlam]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      rcases p3023_3 (m.d 0 3) (by simp) with h3059 | h3059
                                      · linarith only [h2389, h3059, hlam]
                                      · linarith only [h1, h3059, hlam]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p3023_1]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [h2984, hlam, p3023_0]
                                    · have p3023_0 := h3023c.1
                                      have p3023_1 := h3023c.2.1
                                      have p3023_2 := h3023c.2.2.1
                                      have p3023_3 := h3023c.2.2.2
                                      linarith only [hlam, p3023_0]
                          · linarith only [h3, h3014, hlam]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h0, hlam, p2985_0]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [hlam, p2985_0]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h4, hlam, p2985_0]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h1160, hlam, p2985_1]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h1498, hlam, p2985_0]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h1, hlam, p2985_1]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h0, h1640, hc12, hc34, hlam, hphi, ht23, p2985_1]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [hlam, p2985_0]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h1640, hlam, p2985_1]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h2389, hlam, p2985_1]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h2, hlam, p2985_0]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h0, h2503, h2877, h2983, hc12, hc34, hlam, hphi, ht23, p2985_1]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h2503, h2877, h2983, hc03, hc34, hlam, hphi, p2985_1]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [hlam, p2985_0]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h2503, hlam, p2985_0]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h3, hlam, p2985_0]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h0, h2503, h2877, h2983, hc12, hc34, hlam, hphi, ht23, p2985_1]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h1, h2503, h2867, h2877, h2983, hc12, hc34, hlam, hphi, ht23, p2985_1]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [h2, h2503, h2867, h2871, h2877, h2983, hc12, hc34, hlam, hphi, ht23, p2985_1]
                        · have p2985_0 := h2985c.1
                          have p2985_1 := h2985c.2.1
                          have p2985_2 := h2985c.2.2.1
                          have p2985_3 := h2985c.2.2.2
                          linarith only [hlam, p2985_0]
                      · linarith only [h2877, h2983, h2984, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3087 | h3087
                      · linarith only [h0, h2877, h2983, h3087, h4, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h2877, h3087, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1160 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1498 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h1640 | h1640
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h1160 h1498 h1640
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h1160 h1498 h1640

set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1160 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1498 | h1498
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h1160 h1498
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h1160 h1498

set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h1160 | h1160
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h1160
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h1160

set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 6340000 in
set_option maxHeartbeats 6340000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s2 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3 m hb0 hb1 hb3 hb4 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3090 | h3090
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3091 | h3091
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3092 | h3092
        · linarith only [h0, h3, h3092, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3094 | h3094
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3095 | h3095
            · linarith only [h1, h3, h3095, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3097 | h3097
              · linarith only [h2, h3, h3097, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3099 | h3099
                · linarith only [h0, h3, h3099, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · linarith only [h0, h3, h3090, h3099, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3102 | h3102
            · linarith only [h0, h3, h3091, h3094, h3102, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3104 | h3104
              · linarith only [h0, h3, h3091, h3104, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3106 | h3106
                · linarith only [h0, h3, h3106, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · linarith only [h0, h3, h3090, h3106, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3109 | h3109
        · linarith only [h2, h3, h3091, h3109, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3111 | h3111
          · linarith only [h3090, h3091, h3111, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3113 | h3113
            · linarith only [h2, h3, h3090, h3091, h3113, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3115 | h3115
              · linarith only [h2, h3, h3115, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3117 | h3117
                · linarith only [h0, h3, h3117, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · linarith only [h2, h3, h3090, h3091, h3117, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3120 | h3120
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3121 | h3121
        · linarith only [h0, h3, h3121, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3123 | h3123
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3124 | h3124
            · linarith only [h1, h3, h3124, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3126 | h3126
              · linarith only [h1, h3, h3090, h3120, h3126, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3128 | h3128
                · linarith only [h3090, h3120, h3128, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3130 | h3130
                  · linarith only [h1, h3, h3128, h3130, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                  · linarith only [h3090, h3120, h3130, hc12, hc23, hlam, hphi]
          · linarith only [h3090, h3120, h3123, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3134 | h3134
        · linarith only [h1, h3, h3090, h3134, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3136 | h3136
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3137 | h3137
            · linarith only [h1, h3, h3137, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3139 | h3139
              · linarith only [h1, h3, h3136, h3139, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3141 | h3141
                · linarith only [h0, h3, h3141, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3143 | h3143
                  · linarith only [h1, h3, h3120, h3141, h3143, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3145 | h3145
                    · linarith only [h1, h3, h3145, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                    · linarith only [h1, h3, h3136, h3145, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3148 | h3148
            · linarith only [h2, h3, h3136, h3148, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3150 | h3150
              · linarith only [h2, h3, h3150, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3152 | h3152
                · linarith only [h0, h3, h3090, h3152, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3154 | h3154
                  · linarith only [h0, h3120, h3154, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3156 | h3156
                    · linarith only [h1, h3, h3090, h3136, h3156, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3158 | h3158
                      · linarith only [h1, h3, h3148, h3158, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3160 | h3160
                        · linarith only [h2, h3, h3136, h3150, h3160, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3162 | h3162
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3163 | h3163
                            · linarith only [h0, h3, h3158, h3163, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h3090, h3136, h3162, h3163, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3166 | h3166
                            · linarith only [h0, h3090, h3148, h3162, h3166, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3168 | h3168
                              · linarith only [h2, h3, h3152, h3156, h3160, h3168, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3170 | h3170
                                · linarith only [h0, h3090, h3162, h3168, h3170, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h3090, h3162, h3170, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
