import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_14S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1_x1_x0_x1 (m : N7Model)
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
    (h1499 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1500 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h2291 | h2291
  · linarith only [h1499, h1500, h2291, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2293 | h2293
    · linarith only [h0, h1499, h2293, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2295 | h2295
      · linarith only [h0, h1025, h2295, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2297 | h2297
        · linarith only [h0, h1371, h2297, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2299 | h2299
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2300 | h2300
            · linarith only [h1, h1500, h2300, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2302 | h2302
              · linarith only [h2, h2291, h2302, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2304 | h2304
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2305 | h2305
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2306 | h2306
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2307 | h2307
                      · linarith only [h0, h1, h1025, h2291, h2299, h2307, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c | h2309c
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [hlam, p2309_0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          rcases p2309_3 (m.d 0 1) (by simp) with h2311 | h2311
                          · rcases p2309_3 (m.d 0 2) (by simp) with h2312 | h2312
                            · linarith only [h0, h2312, hlam]
                            · rcases p2309_3 (m.d 0 3) (by simp) with h2314 | h2314
                              · linarith only [h1, h2314, hlam]
                              · linarith only [h2314, h4, hlam]
                          · linarith only [h0, h2311, hlam]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h1, h2299, hc34, hlam, hphi, ht0b, ht45, ht5b, p2309_1, u0elo0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          rcases p2309_3 (m.d 0 1) (by simp) with h2319 | h2319
                          · rcases p2309_3 (m.d 0 2) (by simp) with h2320 | h2320
                            · linarith only [h0, h2320, hlam]
                            · rcases p2309_3 (m.d 0 3) (by simp) with h2322 | h2322
                              · linarith only [h1, h2322, hlam]
                              · linarith only [h1499, h2322, hlam]
                          · linarith only [h2, h2319, hlam]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h1, h1500, h2299, hc34, hlam, hphi, ht0b, ht45, ht5b, p2309_1, u0elo0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h0, hlam, p2309_0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [hlam, p2309_0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h4, hlam, p2309_0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h1025, hlam, p2309_1]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h1371, hlam, p2309_0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h1, hlam, p2309_1]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h0, h1500, h2304, h2306, h2307, hc12, hc23, hlam, hphi, p2309_1]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [hlam, p2309_0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h0, h1025, h1500, h2304, h2306, h2307, hc12, hc23, hlam, hphi, p2309_1]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h1500, hlam, p2309_1]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h2, hlam, p2309_0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h0, h1499, h1500, h2304, h2306, h2307, hc12, hc23, hlam, hphi, p2309_1]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h1499, hlam, p2309_0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [hlam, p2309_0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h2291, hlam, p2309_0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h3, hlam, p2309_0]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h0, h1500, h2304, h2306, h2307, hc12, hc23, hlam, hphi, p2309_1]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h1, h1500, h2299, h2304, h2306, h2307, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2309_1]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [h1500, h2, h2295, h2304, h2306, h2307, hc12, hc23, hlam, hphi, p2309_1]
                        · have p2309_0 := h2309c.1
                          have p2309_1 := h2309c.2.1
                          have p2309_2 := h2309c.2.2.1
                          have p2309_3 := h2309c.2.2.2
                          linarith only [hlam, p2309_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2347 | h2347
                      · linarith only [h1, h2299, h2306, h2347, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c | h2349c
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [hlam, p2349_0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          rcases p2349_3 (m.d 0 1) (by simp) with h2351 | h2351
                          · rcases p2349_3 (m.d 0 2) (by simp) with h2352 | h2352
                            · linarith only [h0, h2352, hlam]
                            · rcases p2349_3 (m.d 0 3) (by simp) with h2354 | h2354
                              · linarith only [h1, h2354, hlam]
                              · linarith only [h2354, h4, hlam]
                          · linarith only [h0, h2351, hlam]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h1, h2299, hc34, hlam, hphi, ht0b, ht45, ht5b, p2349_1, u0elo0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          rcases p2349_3 (m.d 0 1) (by simp) with h2359 | h2359
                          · rcases p2349_3 (m.d 0 2) (by simp) with h2360 | h2360
                            · linarith only [h0, h2360, hlam]
                            · rcases p2349_3 (m.d 0 3) (by simp) with h2362 | h2362
                              · linarith only [h1, h2362, hlam]
                              · linarith only [h1499, h2362, hlam]
                          · linarith only [h2, h2359, hlam]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h1, h1500, h2299, hc34, hlam, hphi, ht0b, ht45, ht5b, p2349_1, u0elo0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h0, hlam, p2349_0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [hlam, p2349_0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h4, hlam, p2349_0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h1025, hlam, p2349_1]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h1371, hlam, p2349_0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h1, hlam, p2349_1]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h0, h1500, h2305, hc12, hc23, hlam, hphi, p2349_1]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [hlam, p2349_0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h1500, h2, h2295, h2305, hc12, hc23, hlam, hphi, p2349_1]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h1500, hlam, p2349_1]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h2, hlam, p2349_0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h0, h1025, h2306, hc12, hc45, hlam, hphi, ht23, ht34, p2349_1]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h1499, hlam, p2349_0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [hlam, p2349_0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h2291, hlam, p2349_0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h3, hlam, p2349_0]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h0, h1500, h2305, hc12, hc23, hlam, hphi, p2349_1]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h1, h1500, h2299, h2305, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2349_1]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [h0, h1025, h1500, h2305, hc12, hc23, hlam, hphi, p2349_1]
                        · have p2349_0 := h2349c.1
                          have p2349_1 := h2349c.2.1
                          have p2349_2 := h2349c.2.2.1
                          have p2349_3 := h2349c.2.2.2
                          linarith only [hlam, p2349_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2387 | h2387
                    · linarith only [h0, h1025, h2291, h2304, h2305, h2387, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2389 | h2389
                      · linarith only [h0, h1, h1025, h2299, h2387, h2389, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c | h2391c
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          rcases p2391_3 (m.d 0 1) (by simp) with h2393 | h2393
                          · rcases p2391_3 (m.d 0 2) (by simp) with h2394 | h2394
                            · linarith only [h0, h2394, hlam]
                            · rcases p2391_3 (m.d 0 3) (by simp) with h2396 | h2396
                              · linarith only [h1, h2396, hlam]
                              · linarith only [h2396, h4, hlam]
                          · linarith only [h0, h2393, hlam]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h1499, hc34, hlam, hphi, ht0b, ht45, ht5b, p2391_1, u0elo0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          rcases p2391_3 (m.d 0 1) (by simp) with h2401 | h2401
                          · rcases p2391_3 (m.d 0 2) (by simp) with h2402 | h2402
                            · linarith only [h0, h2402, hlam]
                            · rcases p2391_3 (m.d 0 3) (by simp) with h2404 | h2404
                              · linarith only [h1, h2404, hlam]
                              · linarith only [h1499, h2404, hlam]
                          · linarith only [h2, h2401, hlam]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h1, h1500, h2299, hc34, hlam, hphi, ht0b, ht45, ht5b, p2391_1, u0elo0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h0, hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h4, hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h1025, hlam, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h1371, hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h1, hlam, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h0, h2305, h2389, h4, hc12, hc45, hlam, hphi, ht23, ht34, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h0, h1025, h2305, h2389, h4, hc12, hc45, hlam, hphi, ht23, ht34, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h1500, hlam, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2, hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h0, h1499, h2305, h2389, h4, hc12, hc45, hlam, hphi, ht23, ht34, p2391_1]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h1499, hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h2291, hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h3, hlam, p2391_0]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          rcases p2391_3 (m.d 0 1) (by simp) with h2425 | h2425
                          · rcases p2391_3 (m.d 0 2) (by simp) with h2426 | h2426
                            · linarith only [h1371, h2426, hlam]
                            · rcases p2391_3 (m.d 0 3) (by simp) with h2428 | h2428
                              · linarith only [h1500, h2428, hlam]
                              · linarith only [h2428, h4, hlam]
                          · linarith only [h0, h2425, hlam]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [h1, h2299, hc34, hlam, hphi, ht0b, ht45, ht5b, p2391_1, u0elo4]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          rcases p2391_3 (m.d 0 1) (by simp) with h2433 | h2433
                          · rcases p2391_3 (m.d 0 2) (by simp) with h2434 | h2434
                            · linarith only [h1371, h2434, hlam]
                            · rcases p2391_3 (m.d 0 3) (by simp) with h2436 | h2436
                              · linarith only [h1500, h2436, hlam]
                              · linarith only [h1499, h2436, hlam]
                          · linarith only [h2, h2433, hlam]
                        · have p2391_0 := h2391c.1
                          have p2391_1 := h2391c.2.1
                          have p2391_2 := h2391c.2.2.1
                          have p2391_3 := h2391c.2.2.2
                          linarith only [hlam, p2391_0]
                · linarith only [h1, h2299, h2304, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h1499, h1500, h2293, h2299, hc12, hc35, hlam, hphi, ht23]

set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1_x1_x0 (m : N7Model)
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
    (h1499 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h1500 | h1500
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1025 h1371 h1499 h1500
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h1025 h1371 h1499 h1500

end R2N4
