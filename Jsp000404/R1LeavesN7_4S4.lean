import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S2
import Jsp000404.R1LeavesN7_4S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h1383 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1609 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1680 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 5 (by decide) (by decide) with h2378 | h2378
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2379 | h2379
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2380 | h2380
      · linarith only [h0, h1680, h2378, h2380, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2382 | h2382
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2383 | h2383
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2384 | h2384
            · rcases h1bigk with h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c | h2385c
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h0, h1609, h2380, h2382, h4, h6, hlam, p2385_2]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                rcases p2385_3 (m.d 0 1) (by simp) with h2388 | h2388
                · rcases p2385_3 (m.d 1 2) (by simp) with h2389 | h2389
                  · linarith only [h0, h2389, hlam]
                  · rcases p2385_3 (m.d 1 3) (by simp) with h2391 | h2391
                    · linarith only [h2391, hlam, p2385_0]
                    · rcases p2385_3 (m.d 1 4) (by simp) with h2393 | h2393
                      · linarith only [h2, h2393, hlam]
                      · linarith only [h1680, h2393, hlam]
                · linarith only [h2388, hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                rcases p2385_3 (m.d 0 1) (by simp) with h2397 | h2397
                · rcases p2385_3 (m.d 1 2) (by simp) with h2398 | h2398
                  · linarith only [h0, h2398, hlam]
                  · rcases p2385_3 (m.d 1 3) (by simp) with h2400 | h2400
                    · linarith only [h1, h2400, hlam]
                    · rcases p2385_3 (m.d 1 4) (by simp) with h2402 | h2402
                      · linarith only [h2402, hlam, p2385_0]
                      · rcases p2385_3 (m.d 1 5) (by simp) with h2404 | h2404
                        · linarith only [h2404, h3, hlam]
                        · rcases h3bigk with h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h0, h2378, h2384, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h0, h1609, h2382, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h0, h1609, h2380, h2382, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            rcases p2406_3 (m.d 0 3) (by simp) with h2411 | h2411
                            · rcases p2406_3 (m.d 1 3) (by simp) with h2412 | h2412
                              · linarith only [h1, h2412, hlam]
                              · linarith only [h2378, h2412, hlam]
                            · linarith only [h2411, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h1, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h9, hlam, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h1680, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h1, h2384, hc01, hc45, hlam, hphi, ht0b, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h4, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2380, hc13, hc34, hlam, hphi, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2380, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h0, h2380, h2384, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h6, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h0, h2378, h2384, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h0, h2384, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h7, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2378, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2382, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2384, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [hlam, p2406_0]
                · linarith only [h2397, hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                rcases p2385_3 (m.d 0 1) (by simp) with h2437 | h2437
                · rcases p2385_3 (m.d 1 2) (by simp) with h2438 | h2438
                  · linarith only [h0, h2438, hlam]
                  · rcases p2385_3 (m.d 1 3) (by simp) with h2440 | h2440
                    · linarith only [h1, h2440, hlam]
                    · linarith only [h2378, h2440, hlam]
                · linarith only [h2437, hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h0, hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h9, hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h1383, hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h1609, hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h1, hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h0, h1680, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2385_1]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h1680, hlam, p2385_1]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h0, h1680, h4, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p2385_1]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h2, hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                rcases p2385_3 (m.d 0 1) (by simp) with h2455 | h2455
                · rcases p2385_3 (m.d 1 2) (by simp) with h2456 | h2456
                  · linarith only [h1383, h2456, hlam]
                  · rcases p2385_3 (m.d 1 3) (by simp) with h2458 | h2458
                    · linarith only [h1680, h2458, hlam]
                    · linarith only [h2458, h9, hlam]
                · linarith only [h0, h2455, hlam]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h0, h1383, h2378, h2380, h2384, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p2385_1]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                rcases p2385_3 (m.d 0 1) (by simp) with h2464 | h2464
                · rcases p2385_3 (m.d 1 2) (by simp) with h2465 | h2465
                  · linarith only [h1383, h2465, hlam]
                  · rcases p2385_3 (m.d 1 3) (by simp) with h2467 | h2467
                    · linarith only [h1680, h2467, hlam]
                    · linarith only [h2378, h2467, hlam]
                · linarith only [h2464, h3, hlam]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h3, hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h0, h2378, h2380, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2385_1]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h2378, hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [h2379, hlam, p2385_0]
              · have p2385_0 := h2385c.1
                have p2385_1 := h2385c.2.1
                have p2385_2 := h2385c.2.2.1
                have p2385_3 := h2385c.2.2.2
                linarith only [hlam, p2385_0]
            · linarith only [h0, h2380, h2384, h4, h6, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h1383, h2379, h2383, hlam]
        · linarith only [h2378, h2382, h9, hlam]
    · linarith only [h1680, h2378, h2379, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2480 | h2480
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2481 | h2481
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2482 | h2482
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2483 | h2483
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2484 | h2484
            · rcases h1bigk with h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c | h2485c
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h0, h2378, h2481, h2484, h4, h9, hlam, p2485_2]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h0, h2378, h2481, h2484, h4, hlam, p2485_2]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                rcases p2485_3 (m.d 0 1) (by simp) with h2489 | h2489
                · rcases p2485_3 (m.d 1 2) (by simp) with h2490 | h2490
                  · linarith only [h0, h2490, hlam]
                  · rcases p2485_3 (m.d 1 3) (by simp) with h2492 | h2492
                    · linarith only [h1, h2492, hlam]
                    · rcases p2485_3 (m.d 1 4) (by simp) with h2494 | h2494
                      · linarith only [h2494, hlam, p2485_0]
                      · rcases p2485_3 (m.d 1 5) (by simp) with h2496 | h2496
                        · linarith only [h2496, h3, hlam]
                        · rcases h3bigk with h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            rcases p2498_3 (m.d 0 3) (by simp) with h2500 | h2500
                            · rcases p2498_3 (m.d 1 3) (by simp) with h2501 | h2501
                              · linarith only [h1, h2501, hlam]
                              · rcases p2498_3 (m.d 2 3) (by simp) with h2503 | h2503
                                · linarith only [h2503, h4, hlam]
                                · linarith only [h2503, h9, hlam]
                            · linarith only [h1, h2500, hlam]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h0, h2378, h2481, h2484, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2498_1]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h0, h2378, h2484, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2498_1]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h0, h2378, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2498_1]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h1, hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h9, hlam, p2498_1]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h1680, hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h2378, hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h4, hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h9, hc12, hc23, hlam, hphi, p2498_1]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h0, h2378, h2484, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2498_1]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h0, h2378, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2498_1]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h6, hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h9, hc12, hc34, hlam, hphi, ht23, p2498_1]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h2481, hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h0, h2378, h2481, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2498_1]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h7, hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h2482, h9, hc12, hc25, hlam, hphi, p2498_1]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h2482, hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [h2484, hlam, p2498_0]
                          · have p2498_0 := h2498c.1
                            have p2498_1 := h2498c.2.1
                            have p2498_2 := h2498c.2.2.1
                            have p2498_3 := h2498c.2.2.2
                            linarith only [hlam, p2498_0]
                · linarith only [h2489, hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                rcases p2485_3 (m.d 0 1) (by simp) with h2531 | h2531
                · rcases p2485_3 (m.d 1 2) (by simp) with h2532 | h2532
                  · linarith only [h0, h2532, hlam]
                  · rcases p2485_3 (m.d 1 3) (by simp) with h2534 | h2534
                    · linarith only [h1, h2534, hlam]
                    · rcases p2485_3 (m.d 1 4) (by simp) with h2536 | h2536
                      · linarith only [h2, h2536, hlam]
                      · linarith only [h2480, h2536, hlam]
                · linarith only [h2531, hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h0, hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h9, hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h1383, hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h1609, hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h1, hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h0, h1680, h2481, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2485_1]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h1680, hlam, p2485_1]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h2378, hlam, p2485_1]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h2, hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h0, h1680, h2481, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2485_1]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h0, h1680, h2481, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2485_1]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h0, h1680, h2481, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p2485_1]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h3, hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h0, h2378, h2481, h2484, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2485_1]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h0, h2378, h2481, h2484, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2485_1]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [h2480, hlam, p2485_0]
              · have p2485_0 := h2485c.1
                have p2485_1 := h2485c.2.1
                have p2485_2 := h2485c.2.2.1
                have p2485_3 := h2485c.2.2.2
                linarith only [hlam, p2485_0]
            · linarith only [h1680, h2480, h2484, hlam]
          · linarith only [h1680, h2480, h2481, h2483, hlam]
        · linarith only [h0, h1680, h2480, h2481, h2482, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2563 | h2563
        · linarith only [h2378, h2481, h2563, h9, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2565 | h2565
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2566 | h2566
            · rcases h1bigk with h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c | h2567c
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [h0, h2563, h2566, h4, h6, h9, hlam, p2567_2]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                rcases p2567_3 (m.d 0 1) (by simp) with h2570 | h2570
                · rcases p2567_3 (m.d 1 2) (by simp) with h2571 | h2571
                  · linarith only [h0, h2571, hlam]
                  · rcases p2567_3 (m.d 1 3) (by simp) with h2573 | h2573
                    · linarith only [h2573, hlam, p2567_0]
                    · rcases p2567_3 (m.d 1 4) (by simp) with h2575 | h2575
                      · linarith only [h2, h2575, hlam]
                      · linarith only [h1680, h2575, hlam]
                · linarith only [h2570, hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                rcases p2567_3 (m.d 0 1) (by simp) with h2579 | h2579
                · rcases p2567_3 (m.d 1 2) (by simp) with h2580 | h2580
                  · linarith only [h0, h2580, hlam]
                  · rcases p2567_3 (m.d 1 3) (by simp) with h2582 | h2582
                    · linarith only [h1, h2582, hlam]
                    · rcases p2567_3 (m.d 1 4) (by simp) with h2584 | h2584
                      · linarith only [h2584, hlam, p2567_0]
                      · rcases p2567_3 (m.d 1 5) (by simp) with h2586 | h2586
                        · linarith only [h2586, h3, hlam]
                        · rcases h3bigk with h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c | h2588c
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            rcases p2588_3 (m.d 0 3) (by simp) with h2590 | h2590
                            · rcases p2588_3 (m.d 1 3) (by simp) with h2591 | h2591
                              · linarith only [h1, h2591, hlam]
                              · rcases p2588_3 (m.d 2 3) (by simp) with h2593 | h2593
                                · linarith only [h2593, h4, hlam]
                                · linarith only [h2593, h9, hlam]
                            · linarith only [h1, h2590, hlam]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2588_1]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h0, h1680, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2588_1]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h0, h2378, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2588_1]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h1, hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h9, hlam, p2588_1]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h1680, hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h2378, hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h4, hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h9, hc12, hc23, hlam, hphi, p2588_1]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h2481, hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h2563, hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h6, hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h9, hc12, hc34, hlam, hphi, ht23, p2588_1]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2588_1]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h0, h2563, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2588_1]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h7, hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h9, hc12, hc35, hlam, hphi, ht23, p2588_1]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h0, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2588_1]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [h2566, hlam, p2588_0]
                          · have p2588_0 := h2588c.1
                            have p2588_1 := h2588c.2.1
                            have p2588_2 := h2588c.2.2.1
                            have p2588_3 := h2588c.2.2.2
                            linarith only [hlam, p2588_0]
                · linarith only [h2579, hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                rcases p2567_3 (m.d 0 1) (by simp) with h2621 | h2621
                · rcases p2567_3 (m.d 1 2) (by simp) with h2622 | h2622
                  · linarith only [h0, h2622, hlam]
                  · rcases p2567_3 (m.d 1 3) (by simp) with h2624 | h2624
                    · linarith only [h1, h2624, hlam]
                    · rcases p2567_3 (m.d 1 4) (by simp) with h2626 | h2626
                      · linarith only [h2, h2626, hlam]
                      · linarith only [h2480, h2626, hlam]
                · linarith only [h2621, hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [h0, hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [h9, hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [h1383, hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [h1609, hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [h1, hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [h0, h1680, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2567_1]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [h1680, hlam, p2567_1]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [h2378, hlam, p2567_1]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [h2, hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                rcases p2567_3 (m.d 0 1) (by simp) with h2641 | h2641
                · rcases p2567_3 (m.d 1 2) (by simp) with h2642 | h2642
                  · linarith only [h1383, h2642, hlam]
                  · rcases p2567_3 (m.d 1 3) (by simp) with h2644 | h2644
                    · linarith only [h1680, h2644, hlam]
                    · linarith only [h2644, h9, hlam]
                · linarith only [h0, h2641, hlam]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                rcases p2567_3 (m.d 0 1) (by simp) with h2648 | h2648
                · rcases p2567_3 (m.d 1 2) (by simp) with h2649 | h2649
                  · linarith only [h1383, h2649, hlam]
                  · rcases p2567_3 (m.d 1 3) (by simp) with h2651 | h2651
                    · linarith only [h1680, h2651, hlam]
                    · rcases p2567_3 (m.d 1 4) (by simp) with h2653 | h2653
                      · rcases p2567_3 (m.d 1 5) (by simp) with h2654 | h2654
                        · linarith only [h2480, h2654, hlam]
                        · linarith only [h2378, h2654, hlam]
                      · linarith only [h1680, h2653, hlam]
                · linarith only [h1, h2648, hlam]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                rcases p2567_3 (m.d 0 1) (by simp) with h2660 | h2660
                · rcases p2567_3 (m.d 1 2) (by simp) with h2661 | h2661
                  · linarith only [h1383, h2661, hlam]
                  · rcases p2567_3 (m.d 1 3) (by simp) with h2663 | h2663
                    · linarith only [h1680, h2663, hlam]
                    · rcases p2567_3 (m.d 1 4) (by simp) with h2665 | h2665
                      · rcases p2567_3 (m.d 1 5) (by simp) with h2666 | h2666
                        · linarith only [h2480, h2666, hlam]
                        · rcases h3bigk with h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            rcases p2668_3 (m.d 0 3) (by simp) with h2670 | h2670
                            · rcases p2668_3 (m.d 1 3) (by simp) with h2671 | h2671
                              · linarith only [h1, h2671, hlam]
                              · rcases p2668_3 (m.d 2 3) (by simp) with h2673 | h2673
                                · linarith only [h2673, h4, hlam]
                                · linarith only [h2673, h9, hlam]
                            · linarith only [h1, h2670, hlam]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2668_1]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h0, h1383, h2378, h2481, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2567_1, p2668_1]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h0, h2378, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2668_1]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h1, hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h9, hlam, p2668_1]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h1680, hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h2378, hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h4, hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h9, hc12, hc23, hlam, hphi, p2668_1]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h2481, hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h2563, hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h6, hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h9, hc12, hc34, hlam, hphi, ht23, p2668_1]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2668_1]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h0, h2563, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2668_1]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h7, hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h9, hc12, hc35, hlam, hphi, ht23, p2668_1]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h0, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2668_1]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [h2566, hlam, p2668_0]
                          · have p2668_0 := h2668c.1
                            have p2668_1 := h2668c.2.1
                            have p2668_2 := h2668c.2.2.1
                            have p2668_3 := h2668c.2.2.2
                            linarith only [hlam, p2668_0]
                      · linarith only [h2480, h2665, hlam]
                · linarith only [h2660, h3, hlam]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [h3, hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                rcases p2567_3 (m.d 0 1) (by simp) with h2703 | h2703
                · rcases p2567_3 (m.d 1 2) (by simp) with h2704 | h2704
                  · linarith only [h1609, h2704, hlam]
                  · rcases p2567_3 (m.d 1 3) (by simp) with h2706 | h2706
                    · linarith only [h2378, h2706, hlam]
                    · linarith only [h2706, h9, hlam]
                · linarith only [h0, h2703, hlam]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                rcases p2567_3 (m.d 0 1) (by simp) with h2710 | h2710
                · rcases p2567_3 (m.d 1 2) (by simp) with h2711 | h2711
                  · linarith only [h1609, h2711, hlam]
                  · rcases p2567_3 (m.d 1 3) (by simp) with h2713 | h2713
                    · linarith only [h2378, h2713, hlam]
                    · rcases p2567_3 (m.d 1 4) (by simp) with h2715 | h2715
                      · rcases p2567_3 (m.d 1 5) (by simp) with h2716 | h2716
                        · rcases h3bigk with h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c | h2717c
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            rcases p2717_3 (m.d 0 3) (by simp) with h2719 | h2719
                            · rcases p2717_3 (m.d 1 3) (by simp) with h2720 | h2720
                              · linarith only [h1, h2720, hlam]
                              · rcases p2717_3 (m.d 2 3) (by simp) with h2722 | h2722
                                · linarith only [h2722, h4, hlam]
                                · linarith only [h2722, h9, hlam]
                            · linarith only [h1, h2719, hlam]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2717_1]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h0, h1383, h2481, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2717_1]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h0, h2378, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2717_1]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h1, hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h9, hlam, p2717_1]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h1680, hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h2378, hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h4, hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h9, hc12, hc23, hlam, hphi, p2717_1]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h2481, hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h2563, hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h6, hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h9, hc12, hc34, hlam, hphi, ht23, p2717_1]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2717_1]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h0, h1609, h2563, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2567_1, p2717_1]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h7, hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h9, hc12, hc35, hlam, hphi, ht23, p2717_1]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h0, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2717_1]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [h2566, hlam, p2717_0]
                          · have p2717_0 := h2717c.1
                            have p2717_1 := h2717c.2.1
                            have p2717_2 := h2717c.2.2.1
                            have p2717_3 := h2717c.2.2.2
                            linarith only [hlam, p2717_0]
                        · linarith only [h2378, h2716, hlam]
                      · linarith only [h1680, h2715, hlam]
                · linarith only [h1, h2710, hlam]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [h2480, hlam, p2567_0]
              · have p2567_0 := h2567c.1
                have p2567_1 := h2567c.2.1
                have p2567_2 := h2567c.2.2.1
                have p2567_3 := h2567c.2.2.2
                linarith only [hlam, p2567_0]
            · linarith only [h1680, h2480, h2566, hlam]
          · linarith only [h1383, h2, h2480, h2565, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2756 | h2756
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2757 | h2757
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2758 | h2758
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2759 | h2759
            · linarith only [h1680, h2480, h2756, h2759, h9, hc12, hc23, hlam, hphi]
            · linarith only [h1680, h2758, h2759, h9, hc12, hc24, hlam, hphi]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2762 | h2762
            · linarith only [h2756, h2758, h2762, hlam]
            · rcases h1bigk with h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c | h2764c
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h0, h1680, h2756, h2758, h4, h6, h8, h9, hlam, p2764_2]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h0, h1680, h2756, h2758, h4, h6, h8, hlam, p2764_2]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                rcases p2764_3 (m.d 0 1) (by simp) with h2768 | h2768
                · rcases p2764_3 (m.d 1 2) (by simp) with h2769 | h2769
                  · linarith only [h0, h2769, hlam]
                  · rcases p2764_3 (m.d 1 3) (by simp) with h2771 | h2771
                    · linarith only [h1, h2771, hlam]
                    · rcases p2764_3 (m.d 1 4) (by simp) with h2773 | h2773
                      · linarith only [h2773, hlam, p2764_0]
                      · rcases p2764_3 (m.d 1 5) (by simp) with h2775 | h2775
                        · linarith only [h2775, h3, hlam]
                        · linarith only [h2480, h2775, hlam]
                · linarith only [h2768, hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                rcases p2764_3 (m.d 0 1) (by simp) with h2779 | h2779
                · rcases p2764_3 (m.d 1 2) (by simp) with h2780 | h2780
                  · linarith only [h0, h2780, hlam]
                  · rcases p2764_3 (m.d 1 3) (by simp) with h2782 | h2782
                    · linarith only [h1, h2782, hlam]
                    · rcases p2764_3 (m.d 1 4) (by simp) with h2784 | h2784
                      · linarith only [h2, h2784, hlam]
                      · rcases p2764_3 (m.d 1 5) (by simp) with h2786 | h2786
                        · linarith only [h2786, hlam, p2764_0]
                        · rcases h3bigk with h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c | h2788c
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [hlam, p2788_0]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            rcases p2788_3 (m.d 0 3) (by simp) with h2790 | h2790
                            · rcases p2788_3 (m.d 1 3) (by simp) with h2791 | h2791
                              · linarith only [h1, h2791, hlam]
                              · rcases p2788_3 (m.d 2 3) (by simp) with h2793 | h2793
                                · linarith only [h2793, h4, hlam]
                                · linarith only [h2793, h9, hlam]
                            · linarith only [h1, h2790, hlam]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h0, h2378, h2757, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p2788_1]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h0, h1680, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2788_1]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h0, h2378, h4, hlam, p2764_2, p2788_1]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h1, hlam, p2788_0]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [hlam, p2788_0]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h9, hlam, p2788_1]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h1680, hlam, p2788_0]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h2378, hlam, p2788_0]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h4, hlam, p2788_0]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h9, hc12, hc23, hlam, hphi, p2788_1]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [hlam, p2788_0]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h0, h1680, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2788_1]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h0, h2378, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2788_1]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h6, hlam, p2788_0]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h9, hc12, hc34, hlam, hphi, ht23, p2788_1]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h2756, hlam, p2788_0]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [hlam, p2788_0]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h2762, hlam, p2788_1]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h7, hlam, p2788_0]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h9, hc12, hc35, hlam, hphi, ht23, p2788_1]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h2757, hlam, p2788_0]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [h0, h2757, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2788_1]
                          · have p2788_0 := h2788c.1
                            have p2788_1 := h2788c.2.1
                            have p2788_2 := h2788c.2.2.1
                            have p2788_3 := h2788c.2.2.2
                            linarith only [hlam, p2788_0]
                · linarith only [h2779, hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h0, hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h9, hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h1383, hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h1609, hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h1, hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h1680, hc12, hc34, hlam, hphi, ht23, p2764_1]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h1680, hlam, p2764_1]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h2378, hlam, p2764_1]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h2, hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h0, h1383, h2758, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2764_1]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h0, h1383, h2758, h4, h6, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2764_1]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h2480, hlam, p2764_1]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h3, hlam, p2764_0]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h0, h2378, h2757, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2764_1]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h0, h2378, h2757, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2764_1]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [h0, h2378, h2757, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2764_1]
              · have p2764_0 := h2764c.1
                have p2764_1 := h2764c.2.1
                have p2764_2 := h2764c.2.2.1
                have p2764_3 := h2764c.2.2.2
                linarith only [hlam, p2764_0]
        · linarith only [h0, h1680, h2756, h2757, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2842 | h2842
        · linarith only [h2378, h2756, h2842, h9, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2844 | h2844
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2845 | h2845
            · rcases h1bigk with h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [hlam, p2846_0]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h0, h2842, h2845, h4, h6, h9, hlam, p2846_2]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h0, h1680, h2480, h2756, h2844, h4, h6, hlam, p2846_2]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h0, h2480, h2756, h2844, h4, h6, hlam, p2846_2]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                rcases p2846_3 (m.d 0 1) (by simp) with h2851 | h2851
                · rcases p2846_3 (m.d 1 2) (by simp) with h2852 | h2852
                  · linarith only [h0, h2852, hlam]
                  · rcases p2846_3 (m.d 1 3) (by simp) with h2854 | h2854
                    · linarith only [h1, h2854, hlam]
                    · rcases p2846_3 (m.d 1 4) (by simp) with h2856 | h2856
                      · linarith only [h2, h2856, hlam]
                      · rcases p2846_3 (m.d 1 5) (by simp) with h2858 | h2858
                        · linarith only [h2858, hlam, p2846_0]
                        · rcases h3bigk with h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c | h2860c
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            rcases p2860_3 (m.d 0 3) (by simp) with h2862 | h2862
                            · rcases p2860_3 (m.d 1 3) (by simp) with h2863 | h2863
                              · linarith only [h1, h2863, hlam]
                              · rcases p2860_3 (m.d 2 3) (by simp) with h2865 | h2865
                                · linarith only [h2865, h4, hlam]
                                · linarith only [h2865, h9, hlam]
                            · linarith only [h1, h2862, hlam]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h0, h1680, h2480, h2756, h2844, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h0, h2378, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h1, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h9, hlam, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h1680, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2378, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h4, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h9, hc12, hc23, hlam, hphi, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2756, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2842, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h6, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h9, hc12, hc34, hlam, hphi, ht23, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h0, h2842, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h7, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h9, hc12, hc35, hlam, hphi, ht23, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h0, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2860_1]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [h2845, hlam, p2860_0]
                          · have p2860_0 := h2860c.1
                            have p2860_1 := h2860c.2.1
                            have p2860_2 := h2860c.2.2.1
                            have p2860_3 := h2860c.2.2.2
                            linarith only [hlam, p2860_0]
                · linarith only [h2851, hlam, p2846_0]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h0, hlam, p2846_0]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [hlam, p2846_0]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h9, hlam, p2846_0]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h1383, hlam, p2846_0]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h1609, hlam, p2846_0]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h1, hlam, p2846_0]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h1680, h2480, h2844, hc12, hc24, hlam, hphi, p2846_1]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [hlam, p2846_0]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h1680, hlam, p2846_1]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h2378, hlam, p2846_1]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h2, hlam, p2846_0]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h0, h2480, h2844, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2846_1]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h0, h2480, h2844, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2846_1]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [hlam, p2846_0]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h2480, hlam, p2846_1]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h3, hlam, p2846_0]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h0, h2480, h2844, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2846_1]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h0, h2480, h2844, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2846_1]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [h0, h2480, h2844, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2846_1]
              · have p2846_0 := h2846c.1
                have p2846_1 := h2846c.2.1
                have p2846_2 := h2846c.2.2.1
                have p2846_3 := h2846c.2.2.2
                linarith only [hlam, p2846_0]
            · linarith only [h2756, h2844, h2845, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2914 | h2914
            · linarith only [h0, h1383, h2844, h2914, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h0, h2756, h2914, h4, h6, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h1383 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1609 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h1680 | h1680
  · exact r1l7_11_23_L_I_H_I_s8_x1_x1_x1_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h1383 h1609 h1680
  · exact r1l7_11_23_L_I_H_I_s8_x1_x1_x1_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h1383 h1609 h1680

set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h1383 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h1609 | h1609
  · exact r1l7_11_23_L_I_H_I_s8_x1_x1_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h1383 h1609
  · exact r1l7_11_23_L_I_H_I_s8_x1_x1_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h1383 h1609

set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 4 (by decide) (by decide) with h1383 | h1383
  · exact r1l7_11_23_L_I_H_I_s8_x1_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h1383
  · exact r1l7_11_23_L_I_H_I_s8_x1_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h1383

set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
  · exact r1l7_11_23_L_I_H_I_s8_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9
  · exact r1l7_11_23_L_I_H_I_s8_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9

set_option maxHeartbeats 8294000 in
set_option maxHeartbeats 8294000 in
theorem r1l7_11_23_L_I_H_I_s7_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  exact r1l7_11_23_L_I_H_I_s8 m hb1 hb3 h0 h1 h2 h3 h4 h5 h6 h7 h8

end R2N4
