import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2352 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2353 | h2353
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2354 | h2354
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2355 | h2355
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2356 | h2356
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2357 | h2357
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2358 | h2358
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2359 | h2359
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2360 | h2360
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2361 | h2361
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2362 | h2362
                    · linarith only [h0, h2353, h2362, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h2352, h2358, h2360, h2362, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h2352, h2358, h2360, h2361, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2366 | h2366
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2367 | h2367
                    · linarith only [h2353, h2360, h2367, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h0bigk with h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c | h2369c
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [hlam, p2369_0]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h0, hlam, p2369_1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2369_1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h0, h2353, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2369_1, u4ehi1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2369_1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p2369_1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [hlam, p2369_0]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h0, h2359, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2369_1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h0, h2353, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2369_1, u4ehi1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h0, h2353, h2360, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2369_1, u4ehi1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h2352, hlam, p2369_1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h2355, hlam, p2369_1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [hlam, p2369_0]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h2353, hc03, hlam, hphi, ht0b, ht45, ht5b, p2369_1, u4ehi1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h0, h2352, h2353, h2360, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2369_1, u4ehi1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h2353, hlam, p2369_0]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h2356, hlam, p2369_0]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h2358, hlam, p2369_0]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [hlam, p2369_0]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h2360, hlam, p2369_0]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h2354, hlam, p2369_0]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h2357, hlam, p2369_1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h2359, hlam, p2369_0]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [h2353, hc05, hlam, hphi, ht0b, ht45, ht5b, p2369_1, u4ehi1]
                      · have p2369_0 := h2369c.1
                        have p2369_1 := h2369c.2.1
                        have p2369_2 := h2369c.2.2.1
                        have p2369_3 := h2369c.2.2.2
                        linarith only [hlam, p2369_0]
                  · linarith only [h0, h2353, h2366, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2396 | h2396
                · linarith only [h2358, h2359, h2396, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2398 | h2398
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2399 | h2399
                    · linarith only [h0, h2353, h2396, h2399, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h0bigk with h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c | h2401c
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [hlam, p2401_0]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h0, hlam, p2401_1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2401_1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h0, h2353, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2401_1, u4ehi1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h0, h2352, h2359, h2398, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2401_1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p2401_1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [hlam, p2401_0]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h0, h2358, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2401_1, u4ehi3]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h0, h2353, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2401_1, u4ehi1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h0, h2354, h2399, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2401_1, u4ehi1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h2352, hlam, p2401_1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h2355, hlam, p2401_1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [hlam, p2401_0]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h2353, hc03, hlam, hphi, ht0b, ht45, ht5b, p2401_1, u4ehi1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h2359, hlam, p2401_1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h2353, hlam, p2401_0]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h2356, hlam, p2401_0]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h2358, hlam, p2401_0]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [hlam, p2401_0]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h2396, hlam, p2401_0]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h2354, hlam, p2401_0]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h2357, hlam, p2401_1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h0, h2352, h2354, h2398, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2401_1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [h0, h2353, h2354, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2401_1, u4ehi1]
                      · have p2401_0 := h2401c.1
                        have p2401_1 := h2401c.2.1
                        have p2401_2 := h2401c.2.2.1
                        have p2401_3 := h2401c.2.2.2
                        linarith only [hlam, p2401_0]
                  · linarith only [h0, h2352, h2358, h2398, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2428 | h2428
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2429 | h2429
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2430 | h2430
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2431 | h2431
                    · linarith only [h0, h2353, h2431, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h2353, h2429, h2431, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h2353, h2429, h2430, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h2358, h2428, h2429, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2436 | h2436
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2437 | h2437
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2438 | h2438
                    · linarith only [h0, h2353, h2438, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h2353, h2436, h2438, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h2353, h2436, h2437, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2442 | h2442
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2443 | h2443
                    · linarith only [h2353, h2436, h2443, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h0bigk with h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [hlam, p2445_0]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h0, hlam, p2445_1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2445_1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h0, h2353, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2445_1, u4ehi1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h0, h2353, h2436, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2445_1, u4ehi1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p2445_1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [hlam, p2445_0]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        rcases p2445_3 (m.d 0 1) (by simp) with h2453 | h2453
                        · linarith only [h0, h2453, hlam]
                        · linarith only [h2352, h2453, hlam]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h0, h2353, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2445_1, u4ehi1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h0, h2353, h2436, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2445_1, u4ehi1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h2352, hlam, p2445_1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h2355, hlam, p2445_1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [hlam, p2445_0]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h2358, hlam, p2445_1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h2428, hlam, p2445_1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h2353, hlam, p2445_0]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h2356, hlam, p2445_0]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h2352, h2436, h2442, hc23, hc45, hlam, hphi, ht34, p2445_1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [hlam, p2445_0]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h2436, hlam, p2445_0]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h2354, hlam, p2445_0]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h2357, hlam, p2445_1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h2352, h2428, h2442, hc23, hc35, hlam, hphi, p2445_1]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [h0, h2354, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2445_1, u4ehi0]
                      · have p2445_0 := h2445c.1
                        have p2445_1 := h2445c.2.1
                        have p2445_2 := h2445c.2.2.1
                        have p2445_3 := h2445c.2.2.2
                        linarith only [hlam, p2445_0]
                  · linarith only [h0, h2353, h2442, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h2354, h2357, hlam]
        · linarith only [h0, h2353, h2356, hlam]
      · linarith only [h0, h2352, h2355, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2477 | h2477
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2478 | h2478
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2479 | h2479
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2480 | h2480
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2481 | h2481
              · linarith only [h2352, h2354, h2481, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2483 | h2483
                · linarith only [h2352, h2354, h2480, h2483, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2485 | h2485
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2486 | h2486
                    · linarith only [h0, h2353, h2483, h2486, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h2353, h2354, h2486, hc45, hlam, hphi, u4ehi1]
                  · linarith only [h0, h2352, h2480, h2485, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2490 | h2490
              · linarith only [h2353, h2354, h2480, h2490, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2492 | h2492
                · linarith only [h2353, h2354, h2492, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2494 | h2494
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2495 | h2495
                    · linarith only [h2353, h2354, h2478, h2492, h2495, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h2353, h2354, h2495, hc45, hlam, hphi, u4ehi1]
                  · linarith only [h0, h2353, h2494, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2499 | h2499
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2500 | h2500
              · linarith only [h2352, h2354, h2500, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2502 | h2502
                · linarith only [h0, h2352, h2479, h2499, h2502, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2504 | h2504
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2505 | h2505
                    · linarith only [h2353, h2502, h2505, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h2353, h2354, h2505, hc45, hlam, hphi, u4ehi1]
                  · linarith only [h0, h2352, h2499, h2504, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2509 | h2509
              · linarith only [h2353, h2354, h2499, h2509, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2511 | h2511
                · linarith only [h0, h2353, h2479, h2511, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2513 | h2513
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2514 | h2514
                    · linarith only [h0, h2353, h2511, h2514, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h2353, h2354, h2514, hc45, hlam, hphi, u4ehi1]
                  · linarith only [h0, h2353, h2513, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · linarith only [h0, h2353, h2478, hlam]
      · linarith only [h0, h2352, h2477, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2520 | h2520
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2521 | h2521
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2522 | h2522
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2523 | h2523
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2524 | h2524
            · linarith only [h2352, h2353, h2524, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2526 | h2526
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2527 | h2527
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2528 | h2528
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2529 | h2529
                    · rcases h0bigk with h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c | h2530c
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [hlam, p2530_0]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h0, hlam, p2530_1]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2530_1]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2353, hlam, p2530_1]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2530_1]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2520, hc02, hc15, hlam, hphi, ht0b, ht5b, p2530_1]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [hlam, p2530_0]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h0, h2526, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2530_1]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h0, h2353, h2520, h2529, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2530_1, u4ehi4]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h0, h2520, h2529, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2530_1, u4ehi4]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2352, hlam, p2530_1]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2521, hlam, p2530_1]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [hlam, p2530_0]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2524, hlam, p2530_1]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2520, h2529, hc03, hlam, hphi, ht0b, ht45, ht5b, p2530_1, u4ehi4]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2520, h2529, hc04, hlam, hphi, ht0b, ht45, ht5b, p2530_1, u4ehi4]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2522, hlam, p2530_0]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2524, hc03, hc34, hlam, hphi, p2530_1]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [hlam, p2530_0]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2520, h2524, h2529, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2530_1, u4ehi4]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2520, hlam, p2530_0]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2523, hlam, p2530_1]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2526, hlam, p2530_0]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [h2527, hlam, p2530_1]
                      · have p2530_0 := h2530c.1
                        have p2530_1 := h2530c.2.1
                        have p2530_2 := h2530c.2.2.1
                        have p2530_3 := h2530c.2.2.2
                        linarith only [hlam, p2530_0]
                    · linarith only [h2352, h2353, h2526, h2527, h2529, hlam]
                  · linarith only [h0, h2521, h2528, hlam]
                · linarith only [h2352, h2353, h2526, h2527, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2559 | h2559
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2560 | h2560
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2561 | h2561
                    · rcases h0bigk with h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c | h2562c
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [hlam, p2562_0]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h0, hlam, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2353, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2353, hlam, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2353, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [hlam, p2562_0]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        rcases p2562_3 (m.d 0 1) (by simp) with h2570 | h2570
                        · linarith only [h0, h2570, hlam]
                        · linarith only [h2352, h2570, hlam]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h0, h2353, h2520, h2561, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2562_1, u4ehi4]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h0, h2520, h2561, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2562_1, u4ehi4]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2352, hlam, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2521, hlam, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [hlam, p2562_0]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2524, hlam, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2526, hlam, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2520, h2561, hc04, hlam, hphi, ht0b, ht45, ht5b, p2562_1, u4ehi4]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2522, hlam, p2562_0]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2352, h2524, h2560, hc23, hc34, hlam, hphi, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [hlam, p2562_0]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2520, h2524, h2561, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2562_1, u4ehi4]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2520, hlam, p2562_0]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2523, hlam, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h0, h2352, h2520, h2560, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [h2559, hlam, p2562_1]
                      · have p2562_0 := h2562c.1
                        have p2562_1 := h2562c.2.1
                        have p2562_2 := h2562c.2.2.1
                        have p2562_3 := h2562c.2.2.2
                        linarith only [hlam, p2562_0]
                    · linarith only [h2352, h2353, h2560, h2561, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2520, h2521, h2559, h2560, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h2353, h2520, h2559, hlam]
          · linarith only [h0, h2520, h2523, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2594 | h2594
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2595 | h2595
            · linarith only [h0, h2352, h2522, h2595, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2597 | h2597
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2598 | h2598
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2599 | h2599
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2600 | h2600
                    · rcases h0bigk with h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c | h2601c
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [hlam, p2601_0]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h0, hlam, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2353, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2353, hlam, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h0, h2520, h2522, h2600, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2601_1, u4ehi4]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2522, hc01, hc24, hlam, hphi, ht12, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [hlam, p2601_0]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2522, h2597, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2522, hlam, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2520, h2522, h2600, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2601_1, u4ehi4]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2352, hlam, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2521, hlam, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [hlam, p2601_0]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2595, hlam, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2520, h2600, hc03, hlam, hphi, ht0b, ht45, ht5b, p2601_1, u4ehi4]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2595, hc01, hc34, hlam, hphi, ht12, ht23, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2595, hc02, hc34, hlam, hphi, ht23, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2595, hc03, hc34, hlam, hphi, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [hlam, p2601_0]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2520, h2595, h2600, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2601_1, u4ehi4]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2520, hlam, p2601_0]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2594, hlam, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2597, hlam, p2601_0]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [h2598, hlam, p2601_1]
                      · have p2601_0 := h2601c.1
                        have p2601_1 := h2601c.2.1
                        have p2601_2 := h2601c.2.2.1
                        have p2601_3 := h2601c.2.2.2
                        linarith only [hlam, p2601_0]
                    · linarith only [h2352, h2353, h2599, h2600, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2352, h2521, h2599, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h2352, h2522, h2597, h2598, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2630 | h2630
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2631 | h2631
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2632 | h2632
                    · rcases h0bigk with h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c | h2633c
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [hlam, p2633_0]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h0, hlam, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2353, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2353, hlam, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2352, h2353, h2597, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2520, h2522, hc04, hc15, hlam, hphi, ht0b, ht5b, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [hlam, p2633_0]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2352, h2522, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2522, hlam, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2520, h2522, h2632, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2633_1, u4ehi4]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2352, hlam, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2521, hlam, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [hlam, p2633_0]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2595, hlam, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2597, hlam, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2520, h2522, h2632, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2633_1, u4ehi4]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2522, hc02, hc24, hlam, hphi, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2352, h2595, hc13, hc34, hlam, hphi, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [hlam, p2633_0]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2520, h2595, h2632, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2633_1, u4ehi4]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2520, hlam, p2633_0]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2594, hlam, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h0, h2352, h2520, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [h2630, hlam, p2633_1]
                      · have p2633_0 := h2633c.1
                        have p2633_1 := h2633c.2.1
                        have p2633_2 := h2633c.2.2.1
                        have p2633_3 := h2633c.2.2.2
                        linarith only [hlam, p2633_0]
                    · linarith only [h2352, h2353, h2631, h2632, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2521, h2631, hlam]
                · linarith only [h0, h2520, h2522, h2630, hlam]
          · linarith only [h0, h2520, h2594, hlam]
      · linarith only [h0, h2352, h2521, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2664 | h2664
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2665 | h2665
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2666 | h2666
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2667 | h2667
            · linarith only [h2352, h2353, h2667, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2669 | h2669
              · linarith only [h2352, h2520, h2669, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2671 | h2671
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2672 | h2672
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2673 | h2673
                    · rcases h0bigk with h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [hlam, p2674_0]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h0, hlam, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2520, h2673, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2353, hlam, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2520, hlam, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [hlam, p2674_0]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        rcases p2674_3 (m.d 0 1) (by simp) with h2682 | h2682
                        · linarith only [h0, h2682, hlam]
                        · linarith only [h2352, h2682, hlam]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2674_1, u4ehi0]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h0, h2352, h2520, h2672, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2352, hlam, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2664, hlam, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [hlam, p2674_0]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2667, hlam, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2669, hlam, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2352, h2672, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2665, hlam, p2674_0]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2352, h2667, h2672, hc23, hc34, hlam, hphi, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [hlam, p2674_0]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2352, h2520, h2667, h2672, hc23, hc34, hlam, hphi, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2352, h2672, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2666, hlam, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2352, h2669, h2672, hc23, hc35, hlam, hphi, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [h2671, hlam, p2674_1]
                      · have p2674_0 := h2674c.1
                        have p2674_1 := h2674c.2.1
                        have p2674_2 := h2674c.2.2.1
                        have p2674_3 := h2674c.2.2.2
                        linarith only [hlam, p2674_0]
                    · linarith only [h2352, h2353, h2672, h2673, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2664, h2672, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2704 | h2704
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2705 | h2705
                    · rcases h0bigk with h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c | h2706c
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [hlam, p2706_0]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h0, hlam, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2353, hlam, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2520, hlam, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [hlam, p2706_0]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        rcases p2706_3 (m.d 0 1) (by simp) with h2714 | h2714
                        · linarith only [h0, h2714, hlam]
                        · linarith only [h2352, h2714, hlam]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2706_1, u4ehi0]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h0, h2352, h2520, h2704, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2352, hlam, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2664, hlam, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [hlam, p2706_0]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2667, hlam, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2669, hlam, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2352, h2704, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2665, hlam, p2706_0]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2352, h2667, h2704, hc23, hc34, hlam, hphi, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [hlam, p2706_0]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2671, hlam, p2706_0]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2352, h2704, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2666, hlam, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2352, h2669, h2704, hc23, hc35, hlam, hphi, p2706_1]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [h2671, h2705, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2706_1, u4ehi0]
                      · have p2706_0 := h2706c.1
                        have p2706_1 := h2706c.2.1
                        have p2706_2 := h2706c.2.2.1
                        have p2706_3 := h2706c.2.2.2
                        linarith only [hlam, p2706_0]
                    · linarith only [h2352, h2353, h2704, h2705, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2352, h2664, h2704, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2736 | h2736
            · linarith only [h2352, h2353, h2736, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2738 | h2738
              · linarith only [h0, h2352, h2666, h2738, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2740 | h2740
                · linarith only [h2665, h2666, h2740, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2742 | h2742
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2743 | h2743
                    · rcases h0bigk with h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c | h2744c
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [hlam, p2744_0]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h0, hlam, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2353, h2740, h2743, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2353, hlam, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2520, hlam, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2352, h2666, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [hlam, p2744_0]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2352, h2666, h2742, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2666, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2744_1, u4ehi0]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2666, hlam, p2744_0]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2352, hlam, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2664, hlam, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [hlam, p2744_0]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2736, hlam, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2738, hlam, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2352, h2742, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2665, hlam, p2744_0]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2352, h2665, h2666, h2742, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [hlam, p2744_0]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2740, hlam, p2744_0]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2352, h2666, h2742, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2666, hc02, hc25, hlam, hphi, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2352, h2738, h2742, hc23, hc35, hlam, hphi, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [h2352, h2353, h2740, h2742, h2743, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2744_1]
                      · have p2744_0 := h2744c.1
                        have p2744_1 := h2744c.2.1
                        have p2744_2 := h2744c.2.2.1
                        have p2744_3 := h2744c.2.2.2
                        linarith only [hlam, p2744_0]
                    · linarith only [h2352, h2353, h2742, h2743, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2352, h2664, h2742, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2772 | h2772
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2773 | h2773
            · linarith only [h0, h2352, h2665, h2773, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2775 | h2775
              · linarith only [h2352, h2520, h2775, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2777 | h2777
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2778 | h2778
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2779 | h2779
                    · rcases h0bigk with h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c | h2780c
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [hlam, p2780_0]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h0, hlam, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2520, h2665, h2772, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2353, hlam, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2520, hlam, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2665, hc01, hc24, hlam, hphi, ht12, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [hlam, p2780_0]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2352, h2665, h2778, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2665, hlam, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2665, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2352, hlam, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2664, hlam, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [hlam, p2780_0]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2773, hlam, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2775, hlam, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2352, h2778, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2665, hc02, hc24, hlam, hphi, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2352, h2773, h2778, hc23, hc34, hlam, hphi, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [hlam, p2780_0]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2352, h2520, h2773, h2778, hc23, hc34, hlam, hphi, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2352, h2772, h2778, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2772, hlam, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2352, h2665, h2772, h2778, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [h2777, hlam, p2780_1]
                      · have p2780_0 := h2780c.1
                        have p2780_1 := h2780c.2.1
                        have p2780_2 := h2780c.2.2.1
                        have p2780_3 := h2780c.2.2.2
                        linarith only [hlam, p2780_0]
                    · linarith only [h2352, h2353, h2773, h2777, h2778, h2779, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h2664, h2778, hlam]
                · linarith only [h2665, h2772, h2777, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2809 | h2809
            · linarith only [h0, h2352, h2665, h2809, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2811 | h2811
              · linarith only [h0, h2352, h2772, h2811, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2813 | h2813
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2814 | h2814
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2815 | h2815
                    · rcases h0bigk with h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c | h2816c
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [hlam, p2816_0]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h0, hlam, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h0, h2772, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2353, hlam, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2520, hlam, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2772, hc01, hc25, hlam, hphi, ht12, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [hlam, p2816_0]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2352, h2772, h2814, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2665, hlam, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2772, hlam, p2816_0]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2352, hlam, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2664, hlam, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [hlam, p2816_0]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2809, hlam, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2811, hlam, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2352, h2814, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2665, hc02, hc24, hlam, hphi, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2352, h2809, h2814, hc23, hc34, hlam, hphi, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [hlam, p2816_0]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h0, h2352, h2772, h2809, h2814, hc23, hc34, hlam, hphi, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2352, h2814, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h0, h2352, h2811, h2814, hc23, hc35, hlam, hphi, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2352, h2811, h2814, hc23, hc35, hlam, hphi, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [h2813, hlam, p2816_1]
                      · have p2816_0 := h2816c.1
                        have p2816_1 := h2816c.2.1
                        have p2816_2 := h2816c.2.2.1
                        have p2816_3 := h2816c.2.2.2
                        linarith only [hlam, p2816_0]
                    · linarith only [h2352, h2353, h2809, h2813, h2814, h2815, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h2664, h2814, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2844 | h2844
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2845 | h2845
                    · rcases h0bigk with h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c | h2846c
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [hlam, p2846_0]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h0, hlam, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h0, h2352, h2844, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2353, hlam, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2520, hlam, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2665, h2813, h2845, hc01, hc14, hlam, hphi, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [hlam, p2846_0]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2352, h2665, h2813, h2844, h2845, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2665, hlam, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2772, hlam, p2846_0]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2352, hlam, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2664, hlam, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [hlam, p2846_0]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2809, hlam, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2811, hlam, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2352, h2813, h2844, h2845, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2813, h2845, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2352, h2813, h2844, h2845, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [hlam, p2846_0]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2813, hlam, p2846_0]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2352, h2813, h2844, h2845, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h0, h2352, h2813, h2844, h2845, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2352, h2813, h2844, h2845, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2846_1]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [h2813, h2845, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2846_1, u4ehi0]
                      · have p2846_0 := h2846c.1
                        have p2846_1 := h2846c.2.1
                        have p2846_2 := h2846c.2.2.1
                        have p2846_3 := h2846c.2.2.2
                        linarith only [hlam, p2846_0]
                    · linarith only [h2352, h2353, h2844, h2845, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2352, h2664, h2844, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · linarith only [h0, h2352, h2664, hlam]

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2352 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2875 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2876 | h2876
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2877 | h2877
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2878 | h2878
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2879 | h2879
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2880 | h2880
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2881 | h2881
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2882 | h2882
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2883 | h2883
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2884 | h2884
                  · linarith only [h2352, h2875, h2884, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h2352, h2875, h2882, h2883, h2884, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h2875, h2877, h2883, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2888 | h2888
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2889 | h2889
                  · linarith only [h2875, h2882, h2889, hlam]
                  · rcases h0bigk with h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h0, hlam, p2891_1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2352, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2875, hc01, hlam, hphi, ht0b, ht45, ht5b, p2891_1, u4ehi1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2352, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p2891_1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2891_1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h0, h2881, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2891_1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h0, h2875, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2891_1, u4ehi1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h0, h2876, h2889, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2891_1, u4ehi1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2876, h2889, hc03, hlam, hphi, ht0b, ht45, ht5b, p2891_1, u4ehi1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2877, hlam, p2891_1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h0, h2875, h2877, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2891_1, u4ehi1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h0, h2876, h2877, h2889, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2891_1, u4ehi1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2875, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2878, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2880, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2882, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2876, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2879, hlam, p2891_1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2881, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2875, hc05, hlam, hphi, ht0b, ht45, ht5b, p2891_1, u4ehi1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [hlam, p2891_0]
                · linarith only [h0, h2877, h2888, hlam]
            · linarith only [h2352, h2876, h2881, hlam]
          · linarith only [h2352, h2875, h2880, hlam]
        · linarith only [h0, h2876, h2879, hlam]
      · linarith only [h2352, h2875, h2877, h2878, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2922 | h2922
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2923 | h2923
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2924 | h2924
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2925 | h2925
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2926 | h2926
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2927 | h2927
                · linarith only [h2877, h2922, h2927, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h2875, h2926, h2927, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2930 | h2930
                · linarith only [h0, h2875, h2877, h2930, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h2875, h2930, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h2876, h2877, h2925, hlam]
          · linarith only [h0, h2875, h2877, h2924, hlam]
        · linarith only [h0, h2876, h2923, hlam]
      · linarith only [h0, h2875, h2922, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2937 | h2937
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2938 | h2938
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2939 | h2939
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2940 | h2940
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2941 | h2941
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2942 | h2942
              · linarith only [h2875, h2876, h2942, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2944 | h2944
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2945 | h2945
                  · linarith only [h2352, h2875, h2942, h2944, h2945, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h2875, h2876, h2945, hc45, hlam, hphi, u4ehi1]
                · linarith only [h0, h2937, h2944, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2949 | h2949
              · linarith only [h2875, h2876, h2949, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2951 | h2951
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2952 | h2952
                  · linarith only [h2875, h2949, h2952, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h2875, h2876, h2952, hc45, hlam, hphi, u4ehi1]
                · linarith only [h0, h2875, h2937, h2941, h2951, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
          · linarith only [h2352, h2875, h2940, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2957 | h2957
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2958 | h2958
            · linarith only [h2937, h2939, h2958, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2960 | h2960
              · linarith only [h2352, h2875, h2937, h2939, h2960, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2962 | h2962
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2963 | h2963
                  · linarith only [h2875, h2960, h2963, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · linarith only [h2875, h2876, h2963, hc45, hlam, hphi, u4ehi1]
                · linarith only [h2937, h2939, h2962, hc12, hc25, hlam, hphi]
          · linarith only [h2352, h2875, h2957, hlam]
      · linarith only [h0, h2875, h2938, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2969 | h2969
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2970 | h2970
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2971 | h2971
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2972 | h2972
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2973 | h2973
              · linarith only [h2875, h2876, h2973, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2975 | h2975
                · linarith only [h2937, h2969, h2975, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h2875, h2975, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h2937, h2970, h2972, hlam]
          · linarith only [h2875, h2876, h2937, h2970, h2971, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2980 | h2980
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2981 | h2981
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2982 | h2982
              · linarith only [h0, h2875, h2970, h2982, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2984 | h2984
                · linarith only [h0, h2875, h2937, h2984, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h2875, h2984, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2987 | h2987
              · linarith only [h2352, h2875, h2981, h2987, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2989 | h2989
                · linarith only [h0, h2875, h2937, h2989, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h2875, h2989, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h2875, h2937, h2980, hlam]
      · linarith only [h0, h2875, h2969, hlam]

end R2N4
