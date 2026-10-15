import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_47S8
import Jsp000404.R1LeavesN7_47S9
import Jsp000404.R1LeavesN7_47S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h664 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1337 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1338 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h2254 | h2254
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2255 | h2255
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2256 | h2256
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2257 | h2257
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2258 | h2258
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2259 | h2259
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2260 | h2260
              · linarith only [h1335, h1338, h2260, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2262 | h2262
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2263 | h2263
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2264 | h2264
                    · rcases h2bigk with h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h0, hlam, p2265_1]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        rcases p2265_3 (m.d 0 2) (by simp) with h2268 | h2268
                        · rcases p2265_3 (m.d 1 2) (by simp) with h2269 | h2269
                          · rcases p2265_3 (m.d 2 3) (by simp) with h2270 | h2270
                            · linarith only [h2270, hlam, p2265_0]
                            · rcases p2265_3 (m.d 2 4) (by simp) with h2272 | h2272
                              · linarith only [h1336, h2272, hlam]
                              · linarith only [h2260, h2272, hlam]
                          · linarith only [h2255, h2269, hlam]
                        · linarith only [h2268, hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        rcases p2265_3 (m.d 0 2) (by simp) with h2277 | h2277
                        · rcases p2265_3 (m.d 1 2) (by simp) with h2278 | h2278
                          · rcases p2265_3 (m.d 2 3) (by simp) with h2279 | h2279
                            · linarith only [h1335, h2279, hlam]
                            · rcases p2265_3 (m.d 2 4) (by simp) with h2281 | h2281
                              · linarith only [h2281, hlam, p2265_0]
                              · rcases p2265_3 (m.d 2 5) (by simp) with h2283 | h2283
                                · linarith only [h1337, h2283, hlam]
                                · rcases h4bigk with h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c | h2285c
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [hlam, p2285_0]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h664, hlam, p2285_0]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h1338, h2255, h2258, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2285_1, u2ehi3]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h1338, hlam, p2285_0]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    rcases p2285_3 (m.d 0 4) (by simp) with h2290 | h2290
                                    · rcases p2285_3 (m.d 1 4) (by simp) with h2291 | h2291
                                      · rcases p2285_3 (m.d 2 4) (by simp) with h2292 | h2292
                                        · linarith only [h1336, h2292, hlam]
                                        · linarith only [h2263, h2292, hlam]
                                      · linarith only [h2259, h2291, hlam]
                                    · linarith only [h2290, hlam, p2285_0]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    rcases p2285_3 (m.d 0 4) (by simp) with h2297 | h2297
                                    · linarith only [h2297, h664, hlam]
                                    · rcases p2285_3 (m.d 1 4) (by simp) with h2299 | h2299
                                      · rcases p2285_3 (m.d 2 4) (by simp) with h2300 | h2300
                                        · linarith only [h2256, h2300, hlam]
                                        · rcases p2285_3 (m.d 3 4) (by simp) with h2302 | h2302
                                          · linarith only [h2258, h2302, hlam]
                                          · linarith only [h1338, h2302, hlam]
                                      · linarith only [h2299, h664, hlam]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [hlam, p2285_0]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    rcases p2285_3 (m.d 0 4) (by simp) with h2307 | h2307
                                    · linarith only [h2307, h664, hlam]
                                    · linarith only [h1336, h2307, hlam]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h1335, h1338, h2255, h2258, h2262, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2285_1]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    rcases p2285_3 (m.d 0 4) (by simp) with h2311 | h2311
                                    · linarith only [h2311, h664, hlam]
                                    · linarith only [h2254, h2311, hlam]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h1336, hlam, p2285_1]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h2256, hlam, p2285_1]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [hlam, p2285_0]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h2260, hlam, p2285_1]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2265_1, p2285_1]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h1335, h1338, h2255, h2258, h2262, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2285_1]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h2258, hlam, p2285_0]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h2255, h2258, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2285_1, u2ehi3]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [hlam, p2285_0]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    rcases p2285_3 (m.d 0 4) (by simp) with h2323 | h2323
                                    · linarith only [h1338, h2323, hlam]
                                    · linarith only [h2254, h2323, hlam]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h2254, hlam, p2285_0]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h2259, hlam, p2285_0]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h2263, hlam, p2285_0]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [h2264, hlam, p2285_0]
                                  · have p2285_0 := h2285c.1
                                    have p2285_1 := h2285c.2.1
                                    have p2285_2 := h2285c.2.2.1
                                    have p2285_3 := h2285c.2.2.2
                                    linarith only [hlam, p2285_0]
                          · linarith only [h2256, h2278, hlam]
                        · linarith only [h2277, hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        rcases p2265_3 (m.d 0 2) (by simp) with h2333 | h2333
                        · rcases p2265_3 (m.d 1 2) (by simp) with h2334 | h2334
                          · rcases p2265_3 (m.d 2 3) (by simp) with h2335 | h2335
                            · linarith only [h1335, h2335, hlam]
                            · linarith only [h2262, h2335, hlam]
                          · linarith only [h2257, h2334, hlam]
                        · linarith only [h2333, hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h1335, h2262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2265_1, u2ehi4]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        rcases p2265_3 (m.d 0 2) (by simp) with h2342 | h2342
                        · linarith only [h0, h2342, hlam]
                        · linarith only [h1335, h2342, hlam]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        rcases p2265_3 (m.d 0 2) (by simp) with h2345 | h2345
                        · linarith only [h0, h2345, hlam]
                        · linarith only [h1336, h2345, hlam]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        rcases p2265_3 (m.d 0 2) (by simp) with h2348 | h2348
                        · linarith only [h0, h2348, hlam]
                        · linarith only [h1337, h2348, hlam]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h1335, hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h2255, hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h2260, hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h1336, h2260, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2265_1, u2ehi4]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h1336, hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h2256, hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h1336, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2265_1, u2ehi2]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [hc24, hlam, hphi, p2265_1, u2ehi4]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h1337, hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h2257, hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h2262, hlam, p2265_1]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [h2263, hlam, p2265_0]
                      · have p2265_0 := h2265c.1
                        have p2265_1 := h2265c.2.1
                        have p2265_2 := h2265c.2.2.1
                        have p2265_3 := h2265c.2.2.2
                        linarith only [hlam, p2265_0]
                    · linarith only [h1335, h1338, h2262, h2264, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                  · linarith only [h1338, h2254, h2255, h2258, h2263, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2368 | h2368
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2369 | h2369
                    · rcases h2bigk with h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c | h2370c
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h0, hlam, p2370_1]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        rcases p2370_3 (m.d 0 2) (by simp) with h2373 | h2373
                        · rcases p2370_3 (m.d 1 2) (by simp) with h2374 | h2374
                          · rcases p2370_3 (m.d 2 3) (by simp) with h2375 | h2375
                            · linarith only [h2375, hlam, p2370_0]
                            · rcases p2370_3 (m.d 2 4) (by simp) with h2377 | h2377
                              · linarith only [h1336, h2377, hlam]
                              · linarith only [h2260, h2377, hlam]
                          · linarith only [h2255, h2374, hlam]
                        · linarith only [h2373, hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        rcases p2370_3 (m.d 0 2) (by simp) with h2382 | h2382
                        · rcases p2370_3 (m.d 1 2) (by simp) with h2383 | h2383
                          · rcases p2370_3 (m.d 2 3) (by simp) with h2384 | h2384
                            · linarith only [h1335, h2384, hlam]
                            · rcases p2370_3 (m.d 2 4) (by simp) with h2386 | h2386
                              · linarith only [h2386, hlam, p2370_0]
                              · rcases p2370_3 (m.d 2 5) (by simp) with h2388 | h2388
                                · linarith only [h1337, h2388, hlam]
                                · rcases h4bigk with h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c | h2390c
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [hlam, p2390_0]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h664, hlam, p2390_0]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h1338, h2255, h2258, h2368, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2390_1]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h1338, hlam, p2390_0]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    rcases p2390_3 (m.d 0 4) (by simp) with h2395 | h2395
                                    · rcases p2390_3 (m.d 1 4) (by simp) with h2396 | h2396
                                      · rcases p2390_3 (m.d 2 4) (by simp) with h2397 | h2397
                                        · linarith only [h1336, h2397, hlam]
                                        · linarith only [h2368, h2397, hlam]
                                      · linarith only [h2259, h2396, hlam]
                                    · linarith only [h2395, hlam, p2390_0]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    rcases p2390_3 (m.d 0 4) (by simp) with h2402 | h2402
                                    · linarith only [h2402, h664, hlam]
                                    · rcases p2390_3 (m.d 1 4) (by simp) with h2404 | h2404
                                      · rcases p2390_3 (m.d 2 4) (by simp) with h2405 | h2405
                                        · linarith only [h2256, h2405, hlam]
                                        · rcases p2390_3 (m.d 3 4) (by simp) with h2407 | h2407
                                          · linarith only [h2258, h2407, hlam]
                                          · linarith only [h1338, h2407, hlam]
                                      · linarith only [h2404, h664, hlam]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [hlam, p2390_0]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    rcases p2390_3 (m.d 0 4) (by simp) with h2412 | h2412
                                    · linarith only [h2412, h664, hlam]
                                    · linarith only [h1336, h2412, hlam]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h1335, h1338, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2390_1, u2ehi2]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    rcases p2390_3 (m.d 0 4) (by simp) with h2416 | h2416
                                    · linarith only [h2416, h664, hlam]
                                    · linarith only [h2254, h2416, hlam]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h1336, hlam, p2390_1]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h2256, hlam, p2390_1]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [hlam, p2390_0]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h2260, hlam, p2390_1]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2370_1, p2390_1]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h1336, hc34, hlam, hphi, ht23, p2390_1, u2ehi3]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h2258, hlam, p2390_0]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h2255, h2258, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2390_1, u2ehi3]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [hlam, p2390_0]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    rcases p2390_3 (m.d 0 4) (by simp) with h2428 | h2428
                                    · linarith only [h1338, h2428, hlam]
                                    · linarith only [h2254, h2428, hlam]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h2254, hlam, p2390_0]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h2259, hlam, p2390_0]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h2368, hlam, p2390_0]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [h2369, hlam, p2390_0]
                                  · have p2390_0 := h2390c.1
                                    have p2390_1 := h2390c.2.1
                                    have p2390_2 := h2390c.2.2.1
                                    have p2390_3 := h2390c.2.2.2
                                    linarith only [hlam, p2390_0]
                          · linarith only [h2256, h2383, hlam]
                        · linarith only [h2382, hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        rcases p2370_3 (m.d 0 2) (by simp) with h2438 | h2438
                        · rcases p2370_3 (m.d 1 2) (by simp) with h2439 | h2439
                          · rcases p2370_3 (m.d 2 3) (by simp) with h2440 | h2440
                            · linarith only [h1335, h2440, hlam]
                            · rcases p2370_3 (m.d 2 4) (by simp) with h2442 | h2442
                              · linarith only [h1336, h2442, hlam]
                              · linarith only [h2368, h2442, hlam]
                          · linarith only [h2257, h2439, hlam]
                        · linarith only [h2438, hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h1335, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2370_1, u2ehi2]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        rcases p2370_3 (m.d 0 2) (by simp) with h2449 | h2449
                        · linarith only [h0, h2449, hlam]
                        · linarith only [h1335, h2449, hlam]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        rcases p2370_3 (m.d 0 2) (by simp) with h2452 | h2452
                        · linarith only [h0, h2452, hlam]
                        · linarith only [h1336, h2452, hlam]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        rcases p2370_3 (m.d 0 2) (by simp) with h2455 | h2455
                        · linarith only [h0, h2455, hlam]
                        · linarith only [h1337, h2455, hlam]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h1335, hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h2255, hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h2260, hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h2262, hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h1336, hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h2256, hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h1336, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2370_1, u2ehi2]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h1336, h1338, h2255, h2258, h2262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2370_1, u2ehi2]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h1337, hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h2257, hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [hc25, hlam, hphi, p2370_1, u2ehi2]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [h2368, hlam, p2370_0]
                      · have p2370_0 := h2370c.1
                        have p2370_1 := h2370c.2.1
                        have p2370_2 := h2370c.2.2.1
                        have p2370_3 := h2370c.2.2.2
                        linarith only [hlam, p2370_0]
                    · linarith only [h1335, h1338, h2369, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h1338, h2254, h2255, h2258, h2368, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
            · linarith only [h1338, h2254, h2255, h2258, h2259, h664, hc01, hc12, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2476 | h2476
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2477 | h2477
              · linarith only [h0, h1335, h2258, h2477, h664, hc01, hc12, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2479 | h2479
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2480 | h2480
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2481 | h2481
                    · rcases h2bigk with h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c | h2482c
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h0, hlam, p2482_1]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        rcases p2482_3 (m.d 0 2) (by simp) with h2485 | h2485
                        · rcases p2482_3 (m.d 1 2) (by simp) with h2486 | h2486
                          · rcases p2482_3 (m.d 2 3) (by simp) with h2487 | h2487
                            · linarith only [h2487, hlam, p2482_0]
                            · rcases p2482_3 (m.d 2 4) (by simp) with h2489 | h2489
                              · linarith only [h1336, h2489, hlam]
                              · linarith only [h2477, h2489, hlam]
                          · linarith only [h2255, h2486, hlam]
                        · linarith only [h2485, hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        rcases p2482_3 (m.d 0 2) (by simp) with h2494 | h2494
                        · rcases p2482_3 (m.d 1 2) (by simp) with h2495 | h2495
                          · rcases p2482_3 (m.d 2 3) (by simp) with h2496 | h2496
                            · linarith only [h1335, h2496, hlam]
                            · rcases p2482_3 (m.d 2 4) (by simp) with h2498 | h2498
                              · linarith only [h2498, hlam, p2482_0]
                              · rcases p2482_3 (m.d 2 5) (by simp) with h2500 | h2500
                                · linarith only [h1337, h2500, hlam]
                                · rcases h4bigk with h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c | h2502c
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h664, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h1338, hc34, hlam, hphi, ht23, p2502_1, u2ehi3]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h1338, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    rcases p2502_3 (m.d 0 4) (by simp) with h2507 | h2507
                                    · rcases p2502_3 (m.d 1 4) (by simp) with h2508 | h2508
                                      · rcases p2502_3 (m.d 2 4) (by simp) with h2509 | h2509
                                        · linarith only [h1336, h2509, hlam]
                                        · linarith only [h2480, h2509, hlam]
                                      · linarith only [h2476, h2508, hlam]
                                    · linarith only [h2507, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h1336, h2258, h2477, h2479, hc34, hlam, hphi, ht23, p2502_1, u2ehi4]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2258, h2477, h2479, hc34, hlam, hphi, ht23, p2502_1, u2ehi4]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2258, hlam, p2502_1]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    rcases p2502_3 (m.d 0 4) (by simp) with h2518 | h2518
                                    · linarith only [h2518, h664, hlam]
                                    · linarith only [h2254, h2518, hlam]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h1336, hlam, p2502_1]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2256, hlam, p2502_1]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2477, hlam, p2502_1]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2482_1, p2502_1]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h1336, hc34, hlam, hphi, ht23, p2502_1, u2ehi3]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h664, hc01, hc34, hlam, hphi, ht12, ht23, p2502_1]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [hc34, hlam, hphi, ht23, p2502_1, u2ehi3]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    rcases p2502_3 (m.d 0 4) (by simp) with h2530 | h2530
                                    · linarith only [h1338, h2530, hlam]
                                    · linarith only [h2254, h2530, hlam]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2254, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2476, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2480, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [h2481, hlam, p2502_0]
                                  · have p2502_0 := h2502c.1
                                    have p2502_1 := h2502c.2.1
                                    have p2502_2 := h2502c.2.2.1
                                    have p2502_3 := h2502c.2.2.2
                                    linarith only [hlam, p2502_0]
                          · linarith only [h2256, h2495, hlam]
                        · linarith only [h2494, hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        rcases p2482_3 (m.d 0 2) (by simp) with h2540 | h2540
                        · rcases p2482_3 (m.d 1 2) (by simp) with h2541 | h2541
                          · rcases p2482_3 (m.d 2 3) (by simp) with h2542 | h2542
                            · linarith only [h1335, h2542, hlam]
                            · linarith only [h2479, h2542, hlam]
                          · linarith only [h2257, h2541, hlam]
                        · linarith only [h2540, hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h1335, h2479, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2482_1, u2ehi4]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        rcases p2482_3 (m.d 0 2) (by simp) with h2549 | h2549
                        · linarith only [h0, h2549, hlam]
                        · linarith only [h1335, h2549, hlam]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        rcases p2482_3 (m.d 0 2) (by simp) with h2552 | h2552
                        · linarith only [h0, h2552, hlam]
                        · linarith only [h1336, h2552, hlam]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        rcases p2482_3 (m.d 0 2) (by simp) with h2555 | h2555
                        · linarith only [h0, h2555, hlam]
                        · linarith only [h1337, h2555, hlam]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h1335, hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h2255, hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h2477, hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h1336, h2477, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2482_1, u2ehi4]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h1336, hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h2256, hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h1336, h2479, hc02, hc35, hlam, hphi, ht0b, ht5b, p2482_1]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h0, h1336, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2482_1, u2ehi4]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h1337, hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h2257, hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h2479, hlam, p2482_1]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [h2480, hlam, p2482_0]
                      · have p2482_0 := h2482c.1
                        have p2482_1 := h2482c.2.1
                        have p2482_2 := h2482c.2.2.1
                        have p2482_3 := h2482c.2.2.2
                        linarith only [hlam, p2482_0]
                    · linarith only [h1335, h1338, h2479, h2481, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                  · linarith only [h2254, h2258, h2480, h664, hc34, hlam, hphi, ht23, u2ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2575 | h2575
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2576 | h2576
                    · rcases h2bigk with h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c | h2577c
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h0, hlam, p2577_1]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        rcases p2577_3 (m.d 0 2) (by simp) with h2580 | h2580
                        · rcases p2577_3 (m.d 1 2) (by simp) with h2581 | h2581
                          · rcases p2577_3 (m.d 2 3) (by simp) with h2582 | h2582
                            · linarith only [h2582, hlam, p2577_0]
                            · rcases p2577_3 (m.d 2 4) (by simp) with h2584 | h2584
                              · linarith only [h1336, h2584, hlam]
                              · linarith only [h2477, h2584, hlam]
                          · linarith only [h2255, h2581, hlam]
                        · linarith only [h2580, hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        rcases p2577_3 (m.d 0 2) (by simp) with h2589 | h2589
                        · rcases p2577_3 (m.d 1 2) (by simp) with h2590 | h2590
                          · rcases p2577_3 (m.d 2 3) (by simp) with h2591 | h2591
                            · linarith only [h1335, h2591, hlam]
                            · rcases p2577_3 (m.d 2 4) (by simp) with h2593 | h2593
                              · linarith only [h2593, hlam, p2577_0]
                              · rcases p2577_3 (m.d 2 5) (by simp) with h2595 | h2595
                                · linarith only [h1337, h2595, hlam]
                                · rcases h4bigk with h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c | h2597c
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h664, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2258, h2479, h2575, h664, hc34, hlam, hphi, ht23, p2597_1, u2ehi2]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h1338, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    rcases p2597_3 (m.d 0 4) (by simp) with h2602 | h2602
                                    · rcases p2597_3 (m.d 1 4) (by simp) with h2603 | h2603
                                      · rcases p2597_3 (m.d 2 4) (by simp) with h2604 | h2604
                                        · linarith only [h1336, h2604, hlam]
                                        · linarith only [h2575, h2604, hlam]
                                      · linarith only [h2476, h2603, hlam]
                                    · linarith only [h2602, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h1336, h2258, h2479, h2575, hc34, hlam, hphi, ht23, p2597_1, u2ehi2]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2258, h2479, h2575, hc34, hlam, hphi, ht23, p2597_1, u2ehi2]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2258, hlam, p2597_1]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    rcases p2597_3 (m.d 0 4) (by simp) with h2613 | h2613
                                    · linarith only [h2613, h664, hlam]
                                    · linarith only [h2254, h2613, hlam]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h1336, hlam, p2597_1]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2256, hlam, p2597_1]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2477, hlam, p2597_1]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2577_1, p2597_1]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h1336, h2479, h2575, hc34, hlam, hphi, ht23, p2597_1, u2ehi2]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h0, h2479, h2575, h664, hc01, hc12, hc34, hlam, hphi, ht23, p2577_1, p2597_1, u2ehi2]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2479, h2575, hc34, hlam, hphi, ht23, p2597_1, u2ehi2]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    rcases p2597_3 (m.d 0 4) (by simp) with h2625 | h2625
                                    · linarith only [h1338, h2625, hlam]
                                    · linarith only [h2254, h2625, hlam]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2254, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2476, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2575, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [h2576, hlam, p2597_0]
                                  · have p2597_0 := h2597c.1
                                    have p2597_1 := h2597c.2.1
                                    have p2597_2 := h2597c.2.2.1
                                    have p2597_3 := h2597c.2.2.2
                                    linarith only [hlam, p2597_0]
                          · linarith only [h2256, h2590, hlam]
                        · linarith only [h2589, hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        rcases p2577_3 (m.d 0 2) (by simp) with h2635 | h2635
                        · rcases p2577_3 (m.d 1 2) (by simp) with h2636 | h2636
                          · rcases p2577_3 (m.d 2 3) (by simp) with h2637 | h2637
                            · linarith only [h1335, h2637, hlam]
                            · rcases p2577_3 (m.d 2 4) (by simp) with h2639 | h2639
                              · linarith only [h1336, h2639, hlam]
                              · linarith only [h2575, h2639, hlam]
                          · linarith only [h2257, h2636, hlam]
                        · linarith only [h2635, hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h1335, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2577_1, u2ehi2]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        rcases p2577_3 (m.d 0 2) (by simp) with h2646 | h2646
                        · linarith only [h0, h2646, hlam]
                        · linarith only [h1335, h2646, hlam]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        rcases p2577_3 (m.d 0 2) (by simp) with h2649 | h2649
                        · linarith only [h0, h2649, hlam]
                        · linarith only [h1336, h2649, hlam]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        rcases p2577_3 (m.d 0 2) (by simp) with h2652 | h2652
                        · linarith only [h0, h2652, hlam]
                        · linarith only [h1337, h2652, hlam]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h1335, hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h2255, hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h2477, hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h2479, hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h1336, hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h2256, hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h1336, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2577_1, u2ehi2]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h0, h1336, h2479, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2577_1, u2ehi2]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h1337, hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h2257, hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [hc25, hlam, hphi, p2577_1, u2ehi2]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [h2575, hlam, p2577_0]
                      · have p2577_0 := h2577c.1
                        have p2577_1 := h2577c.2.1
                        have p2577_2 := h2577c.2.2.1
                        have p2577_3 := h2577c.2.2.2
                        linarith only [hlam, p2577_0]
                    · linarith only [h1335, h1338, h2576, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h2254, h2258, h2575, h664, hc34, hlam, hphi, ht23, u2ehi3]
            · linarith only [h0, h1336, h2254, h2476, h664, hc01, hc12, hlam, hphi]
        · linarith only [h0, h1337, h2257, hlam]
      · linarith only [h0, h1336, h2256, hlam]
    · linarith only [h0, h1336, h2255, hc23, hlam, hphi, u2ehi3]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2676 | h2676
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2677 | h2677
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2678 | h2678
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2679 | h2679
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2680 | h2680
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2681 | h2681
              · linarith only [h1335, h1338, h2681, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2683 | h2683
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2684 | h2684
                  · linarith only [h1335, h1336, h1338, h2254, h2683, h2684, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                  · linarith only [h2681, h2683, h2684, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2687 | h2687
                  · linarith only [h0, h1336, h2254, h2687, h664, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2689 | h2689
                    · linarith only [h1335, h1338, h2254, h2689, hc34, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h1335, h1338, h2680, h2689, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h1335, h1338, h2679, h2680, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2693 | h2693
            · linarith only [h1335, h1338, h2254, h2679, h2693, hc34, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2695 | h2695
              · linarith only [h1335, h1338, h2695, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2697 | h2697
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2698 | h2698
                  · linarith only [h2693, h2698, h664, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h2695, h2697, h2698, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2701 | h2701
                  · linarith only [h2693, h2701, h664, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2703 | h2703
                    · linarith only [h1335, h1338, h2693, h2703, h664, hc34, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h1335, h1338, h2703, hc45, hlam, hphi, ht23, ht34, u2ehi2]
        · linarith only [h0, h1335, h2678, hc25, hlam, hphi, u2ehi2]
      · linarith only [h0, h1336, h2677, hlam]
    · linarith only [h0, h1335, h2676, hlam]

set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1_x1_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h664 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1337 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1338 | h1338
  · exact r1l7_22_14_M_IR_L_I_x1_x1_x0_x0_x0_x0 m hb2 hb4 h0 h664 h1335 h1336 h1337 h1338
  · exact r1l7_22_14_M_IR_L_I_x1_x1_x0_x0_x0_x1 m hb2 hb4 h0 h664 h1335 h1336 h1337 h1338

set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1_x1_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h664 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1337 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  linarith only [h1335, h1337, hc25, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1_x1_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h664 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1337 | h1337
  · exact r1l7_22_14_M_IR_L_I_x1_x1_x0_x0_x0 m hb2 hb4 h0 h664 h1335 h1336 h1337
  · exact r1l7_22_14_M_IR_L_I_x1_x1_x0_x0_x1 m hb2 hb4 h0 h664 h1335 h1336 h1337

set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1_x1_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h664 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1336 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  linarith only [h1335, h1336, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h664 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1336 | h1336
  · exact r1l7_22_14_M_IR_L_I_x1_x1_x0_x0 m hb2 hb4 h0 h664 h1335 h1336
  · exact r1l7_22_14_M_IR_L_I_x1_x1_x0_x1 m hb2 hb4 h0 h664 h1335 h1336

set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h664 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1335 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2711 | h2711
  · linarith only [h1335, h2711, hc23, hlam, hphi, u2ehi3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2713 | h2713
    · linarith only [h1335, h2713, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2715 | h2715
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2716 | h2716
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2717 | h2717
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2718 | h2718
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2719 | h2719
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2720 | h2720
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2721 | h2721
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2722 | h2722
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2723 | h2723
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2724 | h2724
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2725 | h2725
                          · rcases h2bigk with h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c | h2726c
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [hlam, p2726_0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h0, hlam, p2726_1]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h1335, hlam, p2726_0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2711, hlam, p2726_0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2713, hlam, p2726_0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              rcases p2726_3 (m.d 0 2) (by simp) with h2732 | h2732
                              · linarith only [h0, h2732, hlam]
                              · rcases p2726_3 (m.d 1 2) (by simp) with h2734 | h2734
                                · rcases p2726_3 (m.d 2 3) (by simp) with h2735 | h2735
                                  · linarith only [h2717, h2735, hlam]
                                  · linarith only [h1335, h2735, hlam]
                                · linarith only [h0, h2734, hlam]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [hlam, p2726_0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2713, h2722, h2724, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2726_1, u2ehi0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2713, h2724, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2726_1, u2ehi0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2713, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2726_1, u2ehi0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [hc23, hlam, hphi, p2726_1, u2ehi0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2717, hlam, p2726_0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [hlam, p2726_0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2713, h2717, h2724, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2726_1, u2ehi0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2713, h2717, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2726_1, u2ehi0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [hc24, hlam, hphi, p2726_1, u2ehi0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2718, hlam, p2726_0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2722, hlam, p2726_1]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [hlam, p2726_0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2713, h2717, h2722, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2726_1, u2ehi0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [hc25, hlam, hphi, p2726_1, u2ehi0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2719, hlam, p2726_0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2723, hlam, p2726_1]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [h2724, hlam, p2726_0]
                            · have p2726_0 := h2726c.1
                              have p2726_1 := h2726c.2.1
                              have p2726_2 := h2726c.2.2.1
                              have p2726_3 := h2726c.2.2.2
                              linarith only [hlam, p2726_0]
                          · rcases h2bigk with h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c | h2758c
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [hlam, p2758_0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h0, hlam, p2758_1]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h1335, hlam, p2758_0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2711, hlam, p2758_0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2713, hlam, p2758_0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              rcases p2758_3 (m.d 0 2) (by simp) with h2764 | h2764
                              · linarith only [h0, h2764, hlam]
                              · rcases p2758_3 (m.d 1 2) (by simp) with h2766 | h2766
                                · rcases p2758_3 (m.d 2 3) (by simp) with h2767 | h2767
                                  · linarith only [h2717, h2767, hlam]
                                  · linarith only [h1335, h2767, hlam]
                                · linarith only [h0, h2766, hlam]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [hlam, p2758_0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2711, h2716, h2722, h2725, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2758_1]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2713, h2724, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2758_1, u2ehi0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2713, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2758_1, u2ehi0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [hc23, hlam, hphi, p2758_1, u2ehi0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2717, hlam, p2758_0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [hlam, p2758_0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2713, h2717, h2724, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2758_1, u2ehi0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2713, h2717, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2758_1, u2ehi0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [hc24, hlam, hphi, p2758_1, u2ehi0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2718, hlam, p2758_0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2722, hlam, p2758_1]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [hlam, p2758_0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2713, h2717, h2722, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2758_1, u2ehi0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [hc25, hlam, hphi, p2758_1, u2ehi0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2719, hlam, p2758_0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2723, hlam, p2758_1]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [h2724, hlam, p2758_0]
                            · have p2758_0 := h2758c.1
                              have p2758_1 := h2758c.2.1
                              have p2758_2 := h2758c.2.2.1
                              have p2758_3 := h2758c.2.2.2
                              linarith only [hlam, p2758_0]
                        · linarith only [h1335, h2715, h2716, h2717, h2724, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1335, h2723, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1335, h2722, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1335, h2715, h2716, h2721, h664, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h1335, h2715, h2717, h2720, hlam]
              · linarith only [h1335, h2717, h2719, hc25, hlam, hphi, u2ehi0]
            · linarith only [h1335, h2717, h2718, hc24, hlam, hphi, u2ehi0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2797 | h2797
            · linarith only [h2717, h2797, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2799 | h2799
              · linarith only [h2717, h2799, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2801 | h2801
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2802 | h2802
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2803 | h2803
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2804 | h2804
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2805 | h2805
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2806 | h2806
                          · rcases h2bigk with h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c | h2807c
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [hlam, p2807_0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h0, hlam, p2807_1]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h1335, hlam, p2807_0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h2711, hlam, p2807_0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h2713, hlam, p2807_0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h2799, h2803, h2805, hc23, hlam, hphi, p2807_1, u2ehi0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [hlam, p2807_0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h2717, hlam, p2807_0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h2797, hlam, p2807_0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h2799, hlam, p2807_0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [hc23, hlam, hphi, p2807_1, u2ehi0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2807_1]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [hlam, p2807_0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h0, h2799, h2805, hc01, hc23, hlam, hphi, ht12, p2807_1]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h0, h2799, hc01, hc23, hlam, hphi, ht12, p2807_1]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [hc24, hlam, hphi, p2807_1, u2ehi0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p2807_1]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h2803, hlam, p2807_1]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [hlam, p2807_0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h0, h2799, h2803, hc01, hc23, hlam, hphi, ht12, p2807_1]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [hc25, hlam, hphi, p2807_1, u2ehi0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2807_1]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h2804, hlam, p2807_1]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [h2805, hlam, p2807_0]
                            · have p2807_0 := h2807c.1
                              have p2807_1 := h2807c.2.1
                              have p2807_2 := h2807c.2.2.1
                              have p2807_3 := h2807c.2.2.2
                              linarith only [hlam, p2807_0]
                          · rcases h2bigk with h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c | h2833c
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [hlam, p2833_0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h0, hlam, p2833_1]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h1335, hlam, p2833_0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h2711, hlam, p2833_0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h2713, hlam, p2833_0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h2717, hc23, hlam, hphi, p2833_1, u2ehi0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [hlam, p2833_0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h2717, hlam, p2833_0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h2797, hlam, p2833_0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h2799, hlam, p2833_0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [hc23, hlam, hphi, p2833_1, u2ehi0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [hc23, hlam, hphi, p2833_1, u2ehi1]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [hlam, p2833_0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [hc23, hlam, hphi, p2833_1, u2ehi3]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h0, h2799, hc01, hc23, hlam, hphi, ht12, p2833_1]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [hc24, hlam, hphi, p2833_1, u2ehi0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p2833_1]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h2803, hlam, p2833_1]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [hlam, p2833_0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h0, h2799, h2803, hc01, hc23, hlam, hphi, ht12, p2833_1]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [hc25, hlam, hphi, p2833_1, u2ehi0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2833_1]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h2804, hlam, p2833_1]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [h2805, hlam, p2833_0]
                            · have p2833_0 := h2833c.1
                              have p2833_1 := h2833c.2.1
                              have p2833_2 := h2833c.2.2.1
                              have p2833_3 := h2833c.2.2.2
                              linarith only [hlam, p2833_0]
                        · linarith only [h2711, h2716, h2805, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1335, h2804, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h0, h2717, h2803, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h2716, h2802, h664, hlam]
                · linarith only [h0, h1335, h2715, h2717, h2801, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2864 | h2864
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2865 | h2865
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2866 | h2866
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2867 | h2867
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2868 | h2868
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2869 | h2869
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2870 | h2870
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2871 | h2871
                        · linarith only [h2711, h2716, h2869, h2871, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h2711, h2871, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h1335, h2870, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1335, h2715, h2869, hlam]
                  · linarith only [h2711, h2865, h2868, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                · linarith only [h1335, h2715, h2864, h2867, hlam]
              · linarith only [h1335, h2864, h2866, hc25, hlam, hphi, u2ehi0]
            · linarith only [h1335, h2864, h2865, hc24, hlam, hphi, u2ehi0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2880 | h2880
            · linarith only [h2864, h2880, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2882 | h2882
              · linarith only [h2864, h2882, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2884 | h2884
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2885 | h2885
                  · linarith only [h2711, h2716, h2864, h2884, h2885, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2887 | h2887
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2888 | h2888
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2889 | h2889
                        · linarith only [h2880, h2885, h2889, hc24, hlam, hphi, u2ehi1]
                        · linarith only [h2711, h2889, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h1335, h2888, hc35, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h1335, h2715, h2887, hlam]
                · linarith only [h0, h1335, h2715, h2864, h2884, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2895 | h2895
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2896 | h2896
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2897 | h2897
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2898 | h2898
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2899 | h2899
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2900 | h2900
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2901 | h2901
                    · linarith only [h1335, h2715, h2896, h2901, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h1335, h2899, h2901, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h2895, h2900, h664, hlam]
                · linarith only [h1335, h2896, h2899, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h2897, h2898, hc25, hlam, hphi, u2ehi3]
            · linarith only [h1335, h2896, h2897, hc24, hlam, hphi, u2ehi0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2908 | h2908
            · linarith only [h2896, h2908, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2910 | h2910
              · linarith only [h2896, h2910, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2912 | h2912
                · linarith only [h1335, h2715, h2896, h2912, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2914 | h2914
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2915 | h2915
                    · linarith only [h2896, h2912, h2915, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h1335, h2915, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h2895, h2914, h664, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2919 | h2919
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2920 | h2920
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2921 | h2921
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2922 | h2922
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2923 | h2923
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2924 | h2924
                    · linarith only [h1335, h2715, h2919, h2924, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h1335, h2924, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h2711, h2920, h2923, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                · linarith only [h1335, h2919, h2922, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h1335, h2919, h2921, hc25, hlam, hphi, u2ehi0]
            · linarith only [h1335, h2919, h2920, hc24, hlam, hphi, u2ehi0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2931 | h2931
            · linarith only [h2919, h2931, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2933 | h2933
              · linarith only [h2919, h2933, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2935 | h2935
                · linarith only [h1335, h2715, h2919, h2935, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2937 | h2937
                  · linarith only [h1335, h2715, h2895, h2931, h2937, hc24, hlam, hphi, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2939 | h2939
                    · linarith only [h1335, h2715, h2939, hc23, hlam, hphi, u2ehi0]
                    · linarith only [h1335, h2939, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h664 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1335 | h1335
  · exact r1l7_22_14_M_IR_L_I_x1_x1_x0 m hb2 hb4 h0 h664 h1335
  · exact r1l7_22_14_M_IR_L_I_x1_x1_x1 m hb2 hb4 h0 h664 h1335

set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h664 | h664
  · exact r1l7_22_14_M_IR_L_I_x1_x0 m hb2 hb4 h0 h664
  · exact r1l7_22_14_M_IR_L_I_x1_x1 m hb2 hb4 h0 h664

set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_14_M_IR_L_I_x0 m hb2 hb4 h0
  · exact r1l7_22_14_M_IR_L_I_x1 m hb2 hb4 h0

end R2N4
