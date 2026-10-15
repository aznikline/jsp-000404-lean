import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_43S1
import Jsp000404.R1LeavesN7_43S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1570 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2095 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2360 | h2360
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2361 | h2361
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2362 | h2362
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2363 | h2363
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2364 | h2364
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2365 | h2365
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2366 | h2366
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2367 | h2367
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2368 | h2368
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2369 | h2369
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2370 | h2370
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2371 | h2371
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2372 | h2372
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2373 | h2373
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2374 | h2374
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2375 | h2375
                                · rcases h5bigk with h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c | h2376c
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [hlam, p2376_0]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2095, hlam, p2376_1]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2095, h2369, h2371, h2373, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2376_1, u3elo1]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2095, h2369, h2371, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2376_1, u3elo1]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h1570, h2365, h2369, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2376_1, u3elo1]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2369, h2371, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2376_1, u3elo1]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [hlam, p2376_0]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2369, h2371, h2373, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2376_1, u3elo1]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2369, h2371, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2376_1, u3elo1]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2369, h2371, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2376_1, u3elo1]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2362, hlam, p2376_1]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2368, hlam, p2376_1]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [hlam, p2376_0]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2362, hc02, hc35, hlam, hphi, ht0b, ht5b, p2376_1]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2095, h2362, h2369, h2371, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2376_1, u3elo1]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2364, hlam, p2376_0]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2370, hlam, p2376_0]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2373, hlam, p2376_0]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [hlam, p2376_0]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2376_1, u3elo4]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2365, hlam, p2376_0]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2371, hlam, p2376_0]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2374, hlam, p2376_0]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [h2375, hlam, p2376_0]
                                  · have p2376_0 := h2376c.1
                                    have p2376_1 := h2376c.2.1
                                    have p2376_2 := h2376c.2.2.1
                                    have p2376_3 := h2376c.2.2.2
                                    linarith only [hlam, p2376_0]
                                · rcases h5bigk with h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c | h2402c
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [hlam, p2402_0]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2095, hlam, p2402_1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2095, h2369, h2371, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2402_1, u3elo1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2095, h2369, h2371, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2402_1, u3elo1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2095, h2369, h2371, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2402_1, u3elo1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2369, h2371, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2402_1, u3elo1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [hlam, p2402_0]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2369, h2371, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2402_1, u3elo1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2369, h2371, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2402_1, u3elo1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2369, h2371, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2402_1, u3elo1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2362, hlam, p2402_1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2368, hlam, p2402_1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [hlam, p2402_0]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2362, hc02, hc35, hlam, hphi, ht0b, ht5b, p2402_1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2095, h2362, h2369, h2371, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2402_1, u3elo1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2364, hlam, p2402_0]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2370, hlam, p2402_0]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2373, hlam, p2402_0]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [hlam, p2402_0]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2375, hlam, p2402_1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2365, hlam, p2402_0]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2371, hlam, p2402_0]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h2374, hlam, p2402_0]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [h1570, h2365, h2369, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2402_1, u3elo1]
                                  · have p2402_0 := h2402c.1
                                    have p2402_1 := h2402c.2.1
                                    have p2402_2 := h2402c.2.2.1
                                    have p2402_3 := h2402c.2.2.2
                                    linarith only [hlam, p2402_0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2428 | h2428
                                · linarith only [h0, h2363, h2374, h2428, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · rcases h5bigk with h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c | h2430c
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [hlam, p2430_0]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2095, hlam, p2430_1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2095, h2369, h2371, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2430_1, u3elo1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2095, h2369, h2371, h2428, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2430_1, u3elo1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2095, h2369, h2371, h2372, h2374, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2430_1, u3elo1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2369, h2371, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2430_1, u3elo1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [hlam, p2430_0]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2369, h2371, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2430_1, u3elo1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2369, h2371, h2428, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2430_1, u3elo1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2369, h2371, h2372, h2374, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2430_1, u3elo1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2362, hlam, p2430_1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2368, hlam, p2430_1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [hlam, p2430_0]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2362, h2428, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2430_1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2374, hlam, p2430_1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2364, hlam, p2430_0]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2370, hlam, p2430_0]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2373, hlam, p2430_0]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [hlam, p2430_0]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2428, hlam, p2430_1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2365, hlam, p2430_0]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h2371, hlam, p2430_0]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h1570, h2365, h2369, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2430_1, u3elo1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [h1570, h2365, h2369, h2428, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2430_1, u3elo1]
                                  · have p2430_0 := h2430c.1
                                    have p2430_1 := h2430c.2.1
                                    have p2430_2 := h2430c.2.2.1
                                    have p2430_3 := h2430c.2.2.2
                                    linarith only [hlam, p2430_0]
                            · linarith only [h0, h2364, h2373, hc23, hlam, hphi, u3elo1]
                          · linarith only [h0, h2363, h2372, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1570, h2365, h2371, hlam]
                      · linarith only [h0, h2364, h2370, hlam]
                    · linarith only [h0, h2363, h2369, hlam]
                  · linarith only [h0, h2362, h2364, h2366, h2368, hlam]
                · linarith only [h0, h2361, h2363, h2366, h2367, hlam]
              · linarith only [h0, h2360, h2366, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2464 | h2464
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2465 | h2465
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2466 | h2466
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2467 | h2467
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2468 | h2468
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2469 | h2469
                        · linarith only [h1570, h2365, h2467, h2469, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2471 | h2471
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2472 | h2472
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2473 | h2473
                              · linarith only [h1570, h2469, h2473, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2475 | h2475
                                · linarith only [h1570, h2360, h2469, h2471, h2475, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases h5bigk with h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c | h2477c
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [hlam, p2477_0]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2095, hlam, p2477_1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h0, h2364, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2477_1, u3elo1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h0, h2364, h2475, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2477_1, u3elo1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2365, hlam, p2477_1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2468, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2477_1, u3elo1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [hlam, p2477_0]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2468, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2477_1, u3elo1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2468, h2475, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2477_1, u3elo1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2469, hlam, p2477_1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2362, hlam, p2477_1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2466, hlam, p2477_1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [hlam, p2477_0]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2362, h2475, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2477_1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2473, hlam, p2477_1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2364, hlam, p2477_0]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2468, hlam, p2477_0]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2472, hlam, p2477_0]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [hlam, p2477_0]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2475, hlam, p2477_1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2365, hc04, hc45, hlam, hphi, p2477_1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2095, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2477_1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2472, h2475, hc34, hc45, hlam, hphi, p2477_1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [h2475, hc34, hc45, hlam, hphi, p2477_1]
                                  · have p2477_0 := h2477c.1
                                    have p2477_1 := h2477c.2.1
                                    have p2477_2 := h2477c.2.2.1
                                    have p2477_3 := h2477c.2.2.2
                                    linarith only [hlam, p2477_0]
                            · linarith only [h0, h2364, h2472, hc23, hlam, hphi, u3elo1]
                          · linarith only [h0, h2363, h2471, hc23, hlam, hphi, u3elo1]
                      · linarith only [h0, h2468, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h2363, h2467, hlam]
                  · linarith only [h0, h1570, h2362, h2364, h2465, h2466, hc01, hlam, hphi, ht12, ht23, u3elo1]
                · linarith only [h0, h2361, h2363, h2464, h2465, hlam]
              · linarith only [h0, h2360, h2464, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2510 | h2510
            · linarith only [h2363, h2364, h2510, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2512 | h2512
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2513 | h2513
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2514 | h2514
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2515 | h2515
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2516 | h2516
                      · linarith only [h2364, h2516, hc03, hlam, hphi, u3elo1]
                      · linarith only [h1570, h2515, h2516, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2363, h2515, hc13, hlam, hphi, u3elo0]
                  · linarith only [h0, h2362, h2364, h2512, h2514, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h0, h2361, h2363, h2364, h2512, h2513, hc01, hlam, hphi, ht12, ht23, u3elo4]
              · linarith only [h2360, h2364, h2512, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2523 | h2523
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2524 | h2524
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2525 | h2525
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2526 | h2526
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2527 | h2527
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2528 | h2528
                    · linarith only [h2363, h2528, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h2528, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h1570, h2362, h2523, h2526, h2527, hc01, hlam, hphi, ht12, ht23, u3elo0]
                · linarith only [h0, h2361, h2363, h2525, h2526, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h2360, h2363, h2525, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h2363, h2523, h2524, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2535 | h2535
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2536 | h2536
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2537 | h2537
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2538 | h2538
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2539 | h2539
                    · linarith only [h2363, h2539, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h2539, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h2362, h2363, h2535, h2536, h2538, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h2361, h2363, h2536, h2537, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h2360, h2363, h2536, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2545 | h2545
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2546 | h2546
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2547 | h2547
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2548 | h2548
                    · linarith only [h2363, h2548, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h2548, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2362, h2523, h2545, h2547, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h2361, h2363, h2545, h2546, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h2360, h2363, h2545, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2554 | h2554
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2555 | h2555
          · linarith only [h2360, h2362, h2555, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2557 | h2557
            · linarith only [h2360, h2362, h2554, h2557, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2559 | h2559
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2560 | h2560
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2561 | h2561
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2562 | h2562
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2563 | h2563
                      · linarith only [h2555, h2563, hc03, hlam, hphi, u3elo1]
                      · linarith only [h0, h2563, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h2562, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2567 | h2567
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2568 | h2568
                      · linarith only [h2555, h2568, hc03, hlam, hphi, u3elo1]
                      · linarith only [h0, h2568, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h2567, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h2361, h2554, h2555, h2560, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h2360, h2555, h2559, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2574 | h2574
          · linarith only [h2360, h2362, h2554, h2574, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2576 | h2576
            · linarith only [h2361, h2362, h2576, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2578 | h2578
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2579 | h2579
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2580 | h2580
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2581 | h2581
                    · linarith only [h2554, h2581, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h2581, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2584 | h2584
                    · linarith only [h0, h2554, h2584, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h0, h2584, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h2361, h2362, h2579, hc12, hc25, hlam, hphi]
              · linarith only [h2360, h2362, h2574, h2578, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2589 | h2589
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2590 | h2590
        · linarith only [h2360, h2361, h2590, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2592 | h2592
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2593 | h2593
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2594 | h2594
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2595 | h2595
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2596 | h2596
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2597 | h2597
                    · linarith only [h2590, h2597, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h2597, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2360, h2361, h2595, h2596, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2601 | h2601
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2602 | h2602
                    · linarith only [h2590, h2592, h2602, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h0, h2602, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2361, h2589, h2601, hc12, hc24, hlam, hphi]
              · linarith only [h2360, h2361, h2590, h2594, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h2360, h2361, h2592, h2593, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2608 | h2608
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2609 | h2609
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2610 | h2610
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2611 | h2611
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2612 | h2612
                    · linarith only [h0, h2590, h2612, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h0, h2612, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2361, h2589, h2610, h2611, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2616 | h2616
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2617 | h2617
                    · linarith only [h2360, h2361, h2590, h2617, hc23, hlam, hphi, u3elo1]
                    · linarith only [h0, h2617, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2361, h2589, h2616, hc12, hc24, hlam, hphi]
              · linarith only [h2360, h2361, h2590, h2609, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h2361, h2589, h2608, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2623 | h2623
        · linarith only [h2360, h2361, h2623, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2625 | h2625
          · linarith only [h2360, h2589, h2623, h2625, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2627 | h2627
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2628 | h2628
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2629 | h2629
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2630 | h2630
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2631 | h2631
                    · linarith only [h2623, h2631, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h2631, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2360, h2361, h2629, h2630, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2635 | h2635
                  · linarith only [h2360, h2589, h2629, h2635, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2637 | h2637
                    · linarith only [h0, h2623, h2637, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h0, h2637, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h2360, h2625, h2628, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2641 | h2641
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2642 | h2642
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2643 | h2643
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2644 | h2644
                    · linarith only [h2623, h2644, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h2644, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2361, h2642, h2643, hc02, hc25, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2648 | h2648
                  · linarith only [h2360, h2589, h2642, h2648, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2650 | h2650
                    · linarith only [h0, h2623, h2650, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h0, h2650, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h2360, h2361, h2641, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2654 | h2654
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2655 | h2655
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2656 | h2656
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2657 | h2657
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2658 | h2658
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2659 | h2659
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2660 | h2660
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2661 | h2661
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2662 | h2662
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2663 | h2663
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2664 | h2664
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2665 | h2665
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2666 | h2666
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2667 | h2667
                              · linarith only [h2360, h2654, h2659, h2667, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h2360, h2654, h2658, h2659, h2665, h2667, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h2360, h2666, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h2360, h2665, hc02, hlam, hphi, ht23, u3elo3]
                        · linarith only [h1570, h2658, h2664, hlam]
                      · linarith only [h2360, h2654, h2657, h2658, h2663, hc13, hlam, hphi, u3elo2]
                    · linarith only [h2360, h2654, h2656, h2659, h2662, hlam]
                  · linarith only [h2360, h2655, h2659, h2661, hlam]
                · linarith only [h2360, h2659, h2660, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2677 | h2677
                · linarith only [h1570, h2659, h2677, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h2360, h2654, h2677, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2680 | h2680
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2681 | h2681
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2682 | h2682
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2683 | h2683
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2684 | h2684
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2685 | h2685
                        · linarith only [h1570, h2658, h2683, h2685, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2687 | h2687
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2688 | h2688
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2689 | h2689
                              · linarith only [h2360, h2654, h2680, h2689, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2691 | h2691
                                · linarith only [h1570, h2360, h2655, h2680, h2685, h2687, h2689, h2691, hc01, hlam, hphi, ht12, ht23, u3elo1]
                                · rcases h5bigk with h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c | h2693c
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [hlam, p2693_0]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2095, hlam, p2693_1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2360, h2655, h2680, h2687, h2689, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2693_1, u3elo1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2360, h2655, h2680, h2691, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2693_1, u3elo1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2658, hlam, p2693_1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2095, hc01, hc15, hlam, hphi, p2693_1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [hlam, p2693_0]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2684, h2687, h2689, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2693_1, u3elo1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2684, h2691, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2693_1, u3elo1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2685, hlam, p2693_1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2655, hlam, p2693_1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2682, hlam, p2693_1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [hlam, p2693_0]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2360, h2655, h2680, h2691, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2693_1, u3elo1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2689, hlam, p2693_1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2657, hlam, p2693_0]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2684, hlam, p2693_0]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2688, hlam, p2693_0]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [hlam, p2693_0]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2691, hlam, p2693_1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h1570, h2658, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2693_1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2095, h2360, h2654, h2680, h2687, hc01, hc34, hc45, hlam, hphi, ht12, ht23, p2693_1, u3elo1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2688, h2691, hc34, hc45, hlam, hphi, p2693_1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [h2691, hc34, hc45, hlam, hphi, p2693_1]
                                  · have p2693_0 := h2693c.1
                                    have p2693_1 := h2693c.2.1
                                    have p2693_2 := h2693c.2.2.1
                                    have p2693_3 := h2693c.2.2.2
                                    linarith only [hlam, p2693_0]
                            · linarith only [h2360, h2688, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h2360, h2687, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h0, h2684, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2360, h2654, h2680, h2683, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h2360, h2655, h2682, hc12, hc23, hlam, hphi]
                · linarith only [h2360, h2654, h2680, h2681, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2725 | h2725
                · linarith only [h1570, h2680, h2725, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h2360, h2654, h2725, hc12, hlam, hphi, ht23, u3elo2]
          · linarith only [h2360, h2655, h2657, hlam]
        · linarith only [h2360, h2654, h2656, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2730 | h2730
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2731 | h2731
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2732 | h2732
            · linarith only [h2654, h2655, h2732, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2734 | h2734
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2735 | h2735
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2736 | h2736
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2737 | h2737
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2738 | h2738
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2739 | h2739
                        · linarith only [h1570, h2732, h2737, h2739, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2741 | h2741
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2742 | h2742
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2743 | h2743
                              · linarith only [h2654, h2655, h2736, h2738, h2739, h2743, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2745 | h2745
                                · linarith only [h1570, h2654, h2655, h2736, h2738, h2739, h2741, h2745, hc01, hlam, hphi, ht12, ht23, u3elo1]
                                · rcases h5bigk with h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2095, hlam, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2655, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2731, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2747_1, u3elo0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2732, hlam, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2738, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2747_1, u3elo1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2655, h2738, hc02, hlam, hphi, ht23, p2747_1, u3elo1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2738, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2747_1, u3elo1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2739, hlam, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2654, h2655, h2741, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2736, hlam, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2736, h2738, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2747_1, u3elo1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2743, hlam, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2731, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2738, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2742, hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [hlam, p2747_0]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2745, hlam, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2654, h2655, h2741, hc34, hc45, hlam, hphi, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2095, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2654, h2655, h2741, hc34, hc45, hlam, hphi, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [h2745, hc34, hc45, hlam, hphi, p2747_1]
                                  · have p2747_0 := h2747c.1
                                    have p2747_1 := h2747c.2.1
                                    have p2747_2 := h2747c.2.2.1
                                    have p2747_3 := h2747c.2.2.2
                                    linarith only [hlam, p2747_0]
                            · linarith only [h2360, h2654, h2741, h2742, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h2360, h2654, h2741, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h2731, h2738, hc13, hlam, hphi, u3elo0]
                    · linarith only [h2360, h2654, h2734, h2737, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h2360, h2654, h2734, h2736, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h2360, h2654, h2734, h2735, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2779 | h2779
                · linarith only [h1570, h2734, h2779, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h2360, h2654, h2779, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2782 | h2782
            · linarith only [h2360, h2654, h2731, h2782, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2784 | h2784
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2785 | h2785
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2786 | h2786
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2787 | h2787
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2788 | h2788
                      · linarith only [h2360, h2654, h2731, h2788, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h0, h2788, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2360, h2654, h2730, h2784, h2787, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h2360, h2654, h2784, h2786, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h2360, h2654, h2784, h2785, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2794 | h2794
                · linarith only [h1570, h2784, h2794, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h2360, h2654, h2794, hc12, hlam, hphi, ht23, u3elo2]
        · linarith only [h2360, h2654, h2730, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2798 | h2798
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2799 | h2799
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2800 | h2800
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2801 | h2801
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2802 | h2802
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2803 | h2803
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2804 | h2804
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2805 | h2805
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2806 | h2806
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2807 | h2807
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2808 | h2808
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2809 | h2809
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2810 | h2810
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2811 | h2811
                                · rcases h5bigk with h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c | h2812c
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2095, hlam, p2812_1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2654, h2798, h2803, h2805, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2812_1, u3elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2654, h2798, h2803, h2805, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2812_1, u3elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2654, h2798, h2803, h2805, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2812_1, u3elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2805, h2807, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2812_1, u3elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2805, h2807, h2809, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2812_1, u3elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2805, h2807, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2812_1, u3elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2805, h2807, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2812_1, u3elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2798, hlam, p2812_1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2804, hlam, p2812_1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2654, h2798, h2803, h2805, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2812_1, u3elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2654, h2798, h2803, h2805, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2812_1, u3elo1]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2800, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2806, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2809, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2812_1, u3elo4]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2801, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2807, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2810, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [h2811, hlam, p2812_0]
                                  · have p2812_0 := h2812c.1
                                    have p2812_1 := h2812c.2.1
                                    have p2812_2 := h2812c.2.2.1
                                    have p2812_3 := h2812c.2.2.2
                                    linarith only [hlam, p2812_0]
                                · linarith only [h2654, h2798, h2803, h2805, h2810, h2811, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · linarith only [h2654, h2798, h2799, h2801, h2810, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h2360, h2809, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h2360, h2799, h2808, hlam]
                        · linarith only [h1570, h2360, h2798, h2801, h2807, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h2654, h2798, h2800, h2803, h2806, hc01, hc12, hlam, hphi]
                    · linarith only [h2360, h2802, h2805, hc02, hlam, hphi, ht23, u3elo3]
                  · linarith only [h2095, h2654, h2798, h2803, h2804, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h2095, h2360, h2798, h2802, h2803, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2847 | h2847
                · linarith only [h2095, h2654, h2798, h2802, h2847, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2849 | h2849
                  · linarith only [h2095, h2802, h2849, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h2360, h2798, h2849, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h2654, h2798, h2801, hlam]
          · linarith only [h2654, h2798, h2799, h2800, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2854 | h2854
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2855 | h2855
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2856 | h2856
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2857 | h2857
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2858 | h2858
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2859 | h2859
                    · linarith only [h2799, h2859, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h2859, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2360, h2798, h2858, hc12, hc23, hlam, hphi]
                · linarith only [h2095, h2360, h2798, h2856, h2857, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2864 | h2864
                · linarith only [h2095, h2654, h2798, h2856, h2864, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2866 | h2866
                  · linarith only [h2095, h2856, h2866, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h2360, h2798, h2866, hc12, hlam, hphi, ht23, u3elo0]
            · linarith only [h2654, h2798, h2855, hlam]
          · linarith only [h2360, h2798, h2854, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2871 | h2871
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2872 | h2872
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2873 | h2873
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2874 | h2874
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2875 | h2875
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2876 | h2876
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2877 | h2877
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2878 | h2878
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2879 | h2879
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2880 | h2880
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2881 | h2881
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2882 | h2882
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2883 | h2883
                                · rcases h5bigk with h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c | h2884c
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [hlam, p2884_0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2095, hlam, p2884_1]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2798, hlam, p2884_0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2872, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2884_1, u3elo0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2360, h2871, h2873, h2874, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2884_1, u3elo1]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2095, h2879, hc01, hc14, hlam, hphi, p2884_1]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [hlam, p2884_0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2798, h2875, h2879, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2884_1]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2877, h2879, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2884_1, u3elo1]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2877, h2879, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2884_1, u3elo1]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2095, hc01, hc25, hlam, hphi, ht12, p2884_1]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2876, hlam, p2884_1]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [hlam, p2884_0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2876, h2877, h2879, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2884_1, u3elo1]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2876, h2877, h2879, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2884_1, u3elo1]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2872, hlam, p2884_0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2878, hlam, p2884_0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2881, hlam, p2884_0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [hlam, p2884_0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2884_1, u3elo4]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2873, hlam, p2884_0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2879, hlam, p2884_0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2882, hlam, p2884_0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [h2883, hlam, p2884_0]
                                  · have p2884_0 := h2884c.1
                                    have p2884_1 := h2884c.2.1
                                    have p2884_2 := h2884c.2.2.1
                                    have p2884_3 := h2884c.2.2.2
                                    linarith only [hlam, p2884_0]
                                · rcases h5bigk with h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2095, hlam, p2910_1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2798, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2095, h2877, h2879, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2910_1, u3elo1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2873, h2883, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p2910_1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2877, h2879, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2910_1, u3elo1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2877, h2879, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2910_1, u3elo1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2877, h2879, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2910_1, u3elo1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2877, h2879, h2883, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2910_1, u3elo1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2873, h2883, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2910_1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2876, hlam, p2910_1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2876, h2877, h2879, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2910_1, u3elo1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2876, h2877, h2879, h2883, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2910_1, u3elo1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2872, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2878, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2881, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2883, hlam, p2910_1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2873, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2879, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2882, hlam, p2910_0]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [h2095, h2873, h2877, h2879, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2910_1, u3elo1]
                                  · have p2910_0 := h2910c.1
                                    have p2910_1 := h2910c.2.1
                                    have p2910_2 := h2910c.2.2.1
                                    have p2910_3 := h2910c.2.2.2
                                    linarith only [hlam, p2910_0]
                              · linarith only [h2654, h2873, h2882, hlam]
                            · linarith only [h2360, h2881, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h2360, h2880, hc02, hlam, hphi, ht23, u3elo3]
                        · linarith only [h1570, h2871, h2873, h2879, hc01, hlam, hphi, ht12, ht23, u3elo0]
                      · linarith only [h2360, h2872, h2874, h2878, hlam]
                    · linarith only [h2360, h2871, h2874, h2877, hlam]
                  · linarith only [h2360, h2874, h2876, hc02, hc25, hlam, hphi]
                · linarith only [h2360, h2874, h2875, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2944 | h2944
                · linarith only [h2654, h2874, h2944, hc02, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2946 | h2946
                  · linarith only [h2798, h2944, h2946, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2948 | h2948
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2949 | h2949
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2950 | h2950
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2951 | h2951
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2952 | h2952
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2953 | h2953
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2954 | h2954
                                · rcases h5bigk with h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c | h2955c
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2095, hlam, p2955_1]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2798, hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h0, h2871, h2873, h2874, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2955_1, u3elo2]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h0, h2871, h2873, h2874, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2955_1, u3elo2]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2874, h2948, h2950, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2955_1, u3elo2]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2946, hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2874, h2948, h2950, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2955_1, u3elo2]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2874, h2948, h2950, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2955_1, u3elo2]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2095, h2951, h2953, hc01, hlam, hphi, ht12, ht23, p2955_1, u3elo2]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2951, h2953, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2955_1, u3elo2]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2951, h2953, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2955_1, u3elo2]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2951, h2953, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2955_1, u3elo2]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2872, hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2949, hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2952, hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2955_1, u3elo4]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2873, hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2950, hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2953, hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [h2954, hlam, p2955_0]
                                  · have p2955_0 := h2955c.1
                                    have p2955_1 := h2955c.2.1
                                    have p2955_2 := h2955c.2.2.1
                                    have p2955_3 := h2955c.2.2.2
                                    linarith only [hlam, p2955_0]
                                · rcases h5bigk with h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [hlam, p2981_0]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2095, hlam, p2981_1]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2798, hlam, p2981_0]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2798, h2951, h2953, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2981_1, u3elo2]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h0, h2871, h2873, h2874, h2954, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2981_1, u3elo2]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2095, hc01, hc15, hlam, hphi, p2981_1]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [hlam, p2981_0]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2946, hlam, p2981_0]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2946, h2951, h2953, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2981_1, u3elo2]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2946, h2951, h2953, h2954, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2981_1, u3elo2]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2873, h2951, h2953, h2954, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2981_1, u3elo2]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2951, h2953, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2981_1, u3elo2]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [hlam, p2981_0]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2951, h2953, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2981_1, u3elo2]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2951, h2953, h2954, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2981_1, u3elo2]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2872, hlam, p2981_0]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2949, hlam, p2981_0]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2952, hlam, p2981_0]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [hlam, p2981_0]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2954, hlam, p2981_1]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2873, hlam, p2981_0]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2950, hlam, p2981_0]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2953, hlam, p2981_0]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [h2798, h2873, h2951, h2953, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2981_1, u3elo2]
                                  · have p2981_0 := h2981c.1
                                    have p2981_1 := h2981c.2.1
                                    have p2981_2 := h2981c.2.2.1
                                    have p2981_3 := h2981c.2.2.2
                                    linarith only [hlam, p2981_0]
                              · linarith only [h0, h2654, h2871, h2873, h2874, h2953, hc02, hlam, hphi, ht23, u3elo2]
                            · linarith only [h0, h2874, h2952, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h2095, h2874, h2948, h2950, h2951, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1570, h2871, h2873, h2950, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h0, h2872, h2949, hlam]
                    · linarith only [h0, h2871, h2948, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3013 | h3013
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3014 | h3014
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3015 | h3015
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3016 | h3016
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3017 | h3017
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3018 | h3018
                        · linarith only [h1570, h2873, h3016, h3018, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3020 | h3020
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3021 | h3021
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3022 | h3022
                              · linarith only [h3014, h3018, h3022, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3024 | h3024
                                · linarith only [h1570, h3018, h3024, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                · rcases h5bigk with h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c | h3026c
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [hlam, p3026_0]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h2095, hlam, p3026_1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h2798, hlam, p3026_0]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h2360, h2872, h3013, h3024, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3026_1, u3elo1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h2873, hlam, p3026_1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h3017, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3026_1, u3elo1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [hlam, p3026_0]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h2798, h2873, h3017, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3026_1, u3elo1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h3017, h3024, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3026_1, u3elo1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h3018, hlam, p3026_1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h1570, h2873, hc01, hc25, hlam, hphi, ht12, p3026_1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h3015, hlam, p3026_1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [hlam, p3026_0]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h3015, h3017, h3024, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3026_1, u3elo1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h3022, hlam, p3026_1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h2872, hlam, p3026_0]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h3017, hlam, p3026_0]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h3021, hlam, p3026_0]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [hlam, p3026_0]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h3024, hlam, p3026_1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h1570, h2873, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3026_1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h2095, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3026_1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h2798, hc02, hc45, hlam, hphi, ht23, ht34, p3026_1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [h3024, hc34, hc45, hlam, hphi, p3026_1]
                                  · have p3026_0 := h3026c.1
                                    have p3026_1 := h3026c.2.1
                                    have p3026_2 := h3026c.2.2.1
                                    have p3026_3 := h3026c.2.2.2
                                    linarith only [hlam, p3026_0]
                            · linarith only [h2360, h3021, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h2360, h3020, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h2872, h3017, hc13, hlam, hphi, u3elo0]
                    · linarith only [h0, h3016, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2360, h3013, h3015, hc02, hc25, hlam, hphi]
                · linarith only [h2360, h3013, h3014, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3058 | h3058
                · linarith only [h2654, h3013, h3058, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3060 | h3060
                  · linarith only [h2798, h3013, h3060, hc02, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3062 | h3062
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3063 | h3063
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h3064 | h3064
                        · linarith only [h1570, h2873, h3062, h3064, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h3066 | h3066
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h3067 | h3067
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h3068 | h3068
                              · linarith only [h1570, h3064, h3066, h3068, hc01, hlam, hphi, ht12, ht23, u3elo2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h3070 | h3070
                                · linarith only [h2871, h3058, h3068, h3070, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases h5bigk with h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c | h3072c
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [hlam, p3072_0]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h2095, hlam, p3072_1]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h2798, hlam, p3072_0]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h0, h2872, h3013, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3072_1, u3elo2]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h2873, hlam, p3072_1]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h2095, hc01, hc15, hlam, hphi, p3072_1]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [hlam, p3072_0]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h3060, hlam, p3072_0]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h3013, h3063, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3072_1, u3elo2]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h3064, hlam, p3072_1]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h1570, h2873, hc01, hc25, hlam, hphi, ht12, p3072_1]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h2095, hc01, hc25, hlam, hphi, ht12, p3072_1]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [hlam, p3072_0]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h3067, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3072_1, u3elo2]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h3068, hlam, p3072_1]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h2872, hlam, p3072_0]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h3063, hlam, p3072_0]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h3067, hlam, p3072_0]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [hlam, p3072_0]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h3070, hlam, p3072_1]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h1570, h2873, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3072_1]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h1570, h3064, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3072_1]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h2798, hc02, hc45, hlam, hphi, ht23, ht34, p3072_1]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [h3070, hc34, hc45, hlam, hphi, p3072_1]
                                  · have p3072_0 := h3072c.1
                                    have p3072_1 := h3072c.2.1
                                    have p3072_2 := h3072c.2.2.1
                                    have p3072_3 := h3072c.2.2.2
                                    linarith only [hlam, p3072_0]
                            · linarith only [h0, h3013, h3067, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h3013, h3066, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h2872, h3063, hlam]
                    · linarith only [h0, h2871, h3062, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3102 | h3102
            · linarith only [h2871, h2872, h3102, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3104 | h3104
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3105 | h3105
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3106 | h3106
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3107 | h3107
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3108 | h3108
                      · linarith only [h2872, h3108, hc03, hlam, hphi, u3elo1]
                      · linarith only [h0, h3108, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h2871, h3104, h3107, hc23, hlam, hphi, u3elo0]
                  · linarith only [h2360, h3104, h3106, hc02, hc25, hlam, hphi]
                · linarith only [h2360, h3104, h3105, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3114 | h3114
                · linarith only [h2654, h3104, h3114, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3116 | h3116
                  · linarith only [h2798, h3104, h3116, hc02, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3118 | h3118
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3119 | h3119
                      · linarith only [h2872, h3119, hc03, hlam, hphi, u3elo1]
                      · linarith only [h0, h3119, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h3118, hc01, hlam, hphi, ht12, ht23, u3elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3123 | h3123
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3124 | h3124
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3125 | h3125
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3126 | h3126
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3127 | h3127
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3128 | h3128
                    · linarith only [h2871, h3128, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h3128, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2654, h3126, h3127, hc02, hc25, hlam, hphi]
                · linarith only [h2360, h3125, h3126, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3133 | h3133
                · linarith only [h2654, h3125, h3133, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3135 | h3135
                  · linarith only [h2798, h3125, h3135, hc02, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3137 | h3137
                    · linarith only [h2871, h3123, h3137, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h0, h3137, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h2871, h3123, h3124, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3141 | h3141
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3142 | h3142
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3143 | h3143
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3144 | h3144
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3145 | h3145
                    · linarith only [h0, h2871, h3145, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h0, h3145, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2654, h3143, h3144, hc02, hc25, hlam, hphi]
                · linarith only [h2360, h3142, h3143, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3150 | h3150
                · linarith only [h2654, h3142, h3150, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3152 | h3152
                  · linarith only [h2798, h3150, h3152, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3154 | h3154
                    · linarith only [h0, h2871, h3142, h3154, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h0, h3154, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3157 | h3157
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3158 | h3158
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3159 | h3159
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3160 | h3160
                    · linarith only [h0, h2871, h3160, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h0, h3160, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2654, h3158, h3159, hc02, hc25, hlam, hphi]
                · linarith only [h2360, h3157, h3158, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3165 | h3165
                · linarith only [h2654, h3157, h3165, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3167 | h3167
                  · linarith only [h2798, h3165, h3167, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3169 | h3169
                    · linarith only [h0, h2871, h3169, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h0, h3169, hc01, hlam, hphi, ht12, ht23, u3elo3]

set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1570 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2095 | h2095
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x1_x1_x0 m hb0 hb2 hb3 hb5 h0 h1570 h2095
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x1_x1_x1 m hb0 hb2 hb3 hb5 h0 h1570 h2095

set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1570 | h1570
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x1_x0 m hb0 hb2 hb3 hb5 h0 h1570
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x1_x1 m hb0 hb2 hb3 hb5 h0 h1570

set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
