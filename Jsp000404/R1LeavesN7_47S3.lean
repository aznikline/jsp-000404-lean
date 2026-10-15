import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_47S0
import Jsp000404.R1LeavesN7_47S1
import Jsp000404.R1LeavesN7_47S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5862000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h903 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1345 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1450 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1580 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h2252 | h2252
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2253 | h2253
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2254 | h2254
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2255 | h2255
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2256 | h2256
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2257 | h2257
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2258 | h2258
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2259 | h2259
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2260 | h2260
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2261 | h2261
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2262 | h2262
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2263 | h2263
                        · linarith only [h2252, h2263, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                        · linarith only [h2254, h2260, h2262, h2263, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2266 | h2266
                        · linarith only [h2260, h2262, h2266, hlam]
                        · rcases h1bigk with h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c | h2268c
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [hlam, p2268_0]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h0, hlam, p2268_0]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h903, hlam, p2268_0]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h1345, hlam, p2268_0]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h1450, hlam, p2268_0]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            rcases p2268_3 (m.d 0 1) (by simp) with h2274 | h2274
                            · linarith only [h2274, hlam, p2268_0]
                            · rcases p2268_3 (m.d 1 2) (by simp) with h2276 | h2276
                              · rcases p2268_3 (m.d 1 3) (by simp) with h2277 | h2277
                                · linarith only [h2254, h2277, hlam]
                                · linarith only [h2277, h903, hlam]
                              · linarith only [h2276, hlam, p2268_0]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [hlam, p2268_0]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h2257, h2259, h2260, h2262, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2268_1, u4ehi3]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h2259, h2260, h2262, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2268_1, u4ehi3]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h1450, hc01, hc12, hlam, hphi, p2268_1]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            rcases p2268_3 (m.d 0 1) (by simp) with h2285 | h2285
                            · linarith only [h2285, hlam, p2268_0]
                            · rcases p2268_3 (m.d 1 2) (by simp) with h2287 | h2287
                              · rcases p2268_3 (m.d 1 3) (by simp) with h2288 | h2288
                                · rcases p2268_3 (m.d 1 4) (by simp) with h2289 | h2289
                                  · linarith only [h2257, h2289, hlam]
                                  · linarith only [h1345, h2289, hlam]
                                · linarith only [h2288, hlam, p2268_0]
                              · linarith only [h0, h2287, hlam]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h2254, hlam, p2268_1]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [hlam, p2268_0]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h2259, h2260, h2262, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p2268_1, u4ehi3]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h2254, h2259, h2260, h2262, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2268_1, u4ehi3]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            rcases p2268_3 (m.d 0 1) (by simp) with h2298 | h2298
                            · linarith only [h2298, hlam, p2268_0]
                            · rcases p2268_3 (m.d 1 2) (by simp) with h2300 | h2300
                              · rcases p2268_3 (m.d 1 3) (by simp) with h2301 | h2301
                                · rcases p2268_3 (m.d 1 4) (by simp) with h2302 | h2302
                                  · rcases p2268_3 (m.d 1 5) (by simp) with h2303 | h2303
                                    · linarith only [h2259, h2303, hlam]
                                    · linarith only [h1450, h2303, hlam]
                                  · linarith only [h2302, hlam, p2268_0]
                                · linarith only [h2301, h903, hlam]
                              · linarith only [h0, h2300, hlam]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h2255, hlam, p2268_1]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h2257, hlam, p2268_0]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [hlam, p2268_0]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h2259, h2260, h2262, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2268_1, u4ehi3]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            rcases p2268_3 (m.d 0 1) (by simp) with h2313 | h2313
                            · linarith only [h2313, hlam, p2268_0]
                            · rcases p2268_3 (m.d 1 2) (by simp) with h2315 | h2315
                              · rcases p2268_3 (m.d 1 3) (by simp) with h2316 | h2316
                                · rcases p2268_3 (m.d 1 4) (by simp) with h2317 | h2317
                                  · rcases p2268_3 (m.d 1 5) (by simp) with h2318 | h2318
                                    · rcases h3bigk with h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c | h2319c
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [hlam, p2319_0]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h903, hlam, p2319_1]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h1580, hlam, p2319_1]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h1580, h2254, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2319_1, u4ehi3]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h1580, h2254, h2266, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2319_1, u4ehi3]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2252, h2254, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2319_1, u4ehi3]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [hlam, p2319_0]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h0, h1580, h2254, hc01, hc12, hlam, hphi, p2319_1]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        rcases p2319_3 (m.d 0 3) (by simp) with h2328 | h2328
                                        · linarith only [h2328, h903, hlam]
                                        · linarith only [h2252, h2328, hlam]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        rcases p2319_3 (m.d 0 3) (by simp) with h2331 | h2331
                                        · linarith only [h2331, h903, hlam]
                                        · linarith only [h2253, h2331, hlam]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2253, h2266, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2319_1, u4ehi3]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2254, hlam, p2319_0]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [hlam, p2319_0]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2254, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2319_1, u4ehi3]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2254, h2266, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2319_1, u4ehi3]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2252, hlam, p2319_0]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2257, hlam, p2319_0]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2260, hlam, p2319_0]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [hlam, p2319_0]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2266, hlam, p2319_1]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2253, hlam, p2319_0]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2258, hlam, p2319_0]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2261, hlam, p2319_0]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [h2253, hlam, hphi, ht0b, ht45, ht5b, p2319_1, u0elo2, u4ehi3]
                                      · have p2319_0 := h2319c.1
                                        have p2319_1 := h2319c.2.1
                                        have p2319_2 := h2319c.2.2.1
                                        have p2319_3 := h2319c.2.2.2
                                        linarith only [hlam, p2319_0]
                                    · linarith only [h2318, hlam, p2268_0]
                                  · linarith only [h1345, h2317, hlam]
                                · linarith only [h2316, h903, hlam]
                              · linarith only [h0, h2315, hlam]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h2256, hlam, p2268_1]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h2258, hlam, p2268_0]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [h2259, hlam, p2268_0]
                          · have p2268_0 := h2268c.1
                            have p2268_1 := h2268c.2.1
                            have p2268_2 := h2268c.2.2.1
                            have p2268_3 := h2268c.2.2.2
                            linarith only [hlam, p2268_0]
                    · linarith only [h1580, h2253, h2261, hlam]
                  · linarith only [h1580, h2252, h2260, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2359 | h2359
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2360 | h2360
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2361 | h2361
                      · linarith only [h1345, h2259, h2361, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2363 | h2363
                        · linarith only [h2252, h2363, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                        · rcases h1bigk with h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h0, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h903, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h1345, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h1450, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            rcases p2365_3 (m.d 0 1) (by simp) with h2371 | h2371
                            · linarith only [h2371, hlam, p2365_0]
                            · rcases p2365_3 (m.d 1 2) (by simp) with h2373 | h2373
                              · rcases p2365_3 (m.d 1 3) (by simp) with h2374 | h2374
                                · linarith only [h2254, h2374, hlam]
                                · linarith only [h2374, h903, hlam]
                              · linarith only [h2373, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h903, hc01, hc12, hlam, hphi, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h1345, hc01, hc12, hlam, hphi, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h1345, h2259, hc01, hc12, hlam, hphi, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            rcases p2365_3 (m.d 0 1) (by simp) with h2382 | h2382
                            · linarith only [h2382, hlam, p2365_0]
                            · rcases p2365_3 (m.d 1 2) (by simp) with h2384 | h2384
                              · rcases p2365_3 (m.d 1 3) (by simp) with h2385 | h2385
                                · rcases p2365_3 (m.d 1 4) (by simp) with h2386 | h2386
                                  · linarith only [h2257, h2386, hlam]
                                  · linarith only [h1345, h2386, hlam]
                                · linarith only [h2385, hlam, p2365_0]
                              · linarith only [h0, h2384, hlam]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2254, hlam, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h1345, hc01, hc13, hlam, hphi, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h1345, h2254, h2259, hc01, hc12, hlam, hphi, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2259, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2255, hlam, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2257, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2259, hlam, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            rcases p2365_3 (m.d 0 1) (by simp) with h2400 | h2400
                            · linarith only [h2400, hlam, p2365_0]
                            · rcases p2365_3 (m.d 1 2) (by simp) with h2402 | h2402
                              · rcases p2365_3 (m.d 1 3) (by simp) with h2403 | h2403
                                · rcases p2365_3 (m.d 1 4) (by simp) with h2404 | h2404
                                  · linarith only [h2259, h2404, hlam]
                                  · linarith only [h1345, h2404, hlam]
                                · linarith only [h2403, h903, hlam]
                              · linarith only [h0, h2402, hlam]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2256, hlam, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h2258, hlam, p2365_0]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [h1345, hc01, hc15, hlam, hphi, p2365_1]
                          · have p2365_0 := h2365c.1
                            have p2365_1 := h2365c.2.1
                            have p2365_2 := h2365c.2.2.1
                            have p2365_3 := h2365c.2.2.2
                            linarith only [hlam, p2365_0]
                    · linarith only [h1580, h2253, h2360, hlam]
                  · linarith only [h0, h1580, h2252, h2359, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h2253, h2258, h903, hlam]
            · linarith only [h1580, h2252, h2254, h2257, hlam]
          · linarith only [h1580, h2252, h2254, h2256, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
        · linarith only [h1580, h2252, h2254, h2255, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2419 | h2419
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2420 | h2420
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2421 | h2421
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2422 | h2422
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2423 | h2423
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2424 | h2424
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2425 | h2425
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2426 | h2426
                      · linarith only [h2254, h2419, h2426, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h2254, h2419, h2423, h2426, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h2253, h2254, h2425, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h2254, h2419, h2423, h2424, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2431 | h2431
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2432 | h2432
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2433 | h2433
                      · linarith only [h2254, h2419, h2433, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2435 | h2435
                        · linarith only [h1345, h2254, h2420, h2423, h2431, h2433, h2435, hc01, hc23, hlam, hphi, ht12]
                        · rcases h1bigk with h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c | h2437c
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h0, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h903, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h1345, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h1450, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2254, hc01, hc23, hlam, hphi, ht12, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2254, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h1345, h2254, hc01, hc23, hlam, hphi, ht12, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h1345, h2254, h2423, hc01, hc23, hlam, hphi, ht12, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            rcases p2437_3 (m.d 0 1) (by simp) with h2448 | h2448
                            · linarith only [h2448, hlam, p2437_0]
                            · rcases p2437_3 (m.d 1 2) (by simp) with h2450 | h2450
                              · linarith only [h2254, h2450, hlam]
                              · linarith only [h0, h2450, hlam]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2420, h2433, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p2437_1, u4ehi2]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h1345, h2254, hc01, hc23, hlam, hphi, ht12, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h1345, h2254, h2423, hc01, hc23, hlam, hphi, ht12, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2423, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2419, hlam, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2421, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2423, hlam, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2254, h2420, hc01, hc23, hlam, hphi, ht12, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2420, hlam, p2437_1]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h2422, hlam, p2437_0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [h1345, h2254, h2420, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2437_1, u4ehi0]
                          · have p2437_0 := h2437c.1
                            have p2437_1 := h2437c.2.1
                            have p2437_2 := h2437c.2.2.1
                            have p2437_3 := h2437c.2.2.2
                            linarith only [hlam, p2437_0]
                    · linarith only [h0, h2254, h2432, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h2252, h2254, h2420, h2431, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
              · linarith only [h2252, h2253, h2422, h903, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi3]
            · linarith only [h2252, h2421, h903, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2471 | h2471
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2472 | h2472
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2473 | h2473
                · linarith only [h2419, h2420, h2473, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2475 | h2475
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2476 | h2476
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2477 | h2477
                      · linarith only [h1345, h2419, h2420, h2473, h2476, h2477, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · linarith only [h2419, h2420, h2477, hc45, hlam, hphi, u4ehi2]
                    · linarith only [h0, h1580, h2253, h2476, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h2252, h2254, h2419, h2475, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
              · linarith only [h2253, h2472, h903, hlam]
            · linarith only [h2252, h2471, h903, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2484 | h2484
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2485 | h2485
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2486 | h2486
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2487 | h2487
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2488 | h2488
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2489 | h2489
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2490 | h2490
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2491 | h2491
                        · linarith only [h2252, h2491, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                        · linarith only [h2419, h2484, h2488, h2490, h2491, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h2419, h2484, h2487, h2490, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h2253, h2254, h2489, h903, hlam]
                  · linarith only [h1450, h2254, h2484, h2488, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h2419, h2484, h2487, hlam]
              · linarith only [h2253, h2486, h903, hlam]
            · linarith only [h2252, h2485, h903, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2500 | h2500
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2501 | h2501
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2502 | h2502
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2503 | h2503
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2504 | h2504
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2505 | h2505
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2506 | h2506
                        · linarith only [h2252, h2506, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                        · rcases h1bigk with h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c | h2508c
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h0, hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h903, hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h1345, hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h1450, hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2484, h2503, h2505, hc01, hc23, hlam, hphi, ht12, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2254, hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2419, hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2484, hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            rcases p2508_3 (m.d 0 1) (by simp) with h2519 | h2519
                            · linarith only [h2519, hlam, p2508_0]
                            · rcases p2508_3 (m.d 1 2) (by simp) with h2521 | h2521
                              · linarith only [h2254, h2521, hlam]
                              · linarith only [h0, h2521, hlam]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h0, hc01, hc13, hlam, hphi, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2254, h2502, h2506, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2508_1, u4ehi3]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h1450, h2254, hc01, hc23, hlam, hphi, ht12, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            rcases p2508_3 (m.d 0 1) (by simp) with h2528 | h2528
                            · linarith only [h2528, hlam, p2508_0]
                            · rcases p2508_3 (m.d 1 2) (by simp) with h2530 | h2530
                              · linarith only [h2419, h2530, hlam]
                              · linarith only [h0, h2530, hlam]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2500, hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2419, h2502, h2503, h2506, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2508_1, u4ehi3]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            rcases p2508_3 (m.d 0 1) (by simp) with h2537 | h2537
                            · linarith only [h2537, hlam, p2508_0]
                            · rcases p2508_3 (m.d 1 2) (by simp) with h2539 | h2539
                              · linarith only [h2484, h2539, hlam]
                              · linarith only [h0, h2539, hlam]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p2508_1]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2501, hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [h2502, hlam, p2508_0]
                          · have p2508_0 := h2508c.1
                            have p2508_1 := h2508c.2.1
                            have p2508_2 := h2508c.2.2.1
                            have p2508_3 := h2508c.2.2.2
                            linarith only [hlam, p2508_0]
                      · linarith only [h0, h2419, h2505, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h2253, h2254, h2504, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h2252, h2254, h2503, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2549 | h2549
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2550 | h2550
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2551 | h2551
                      · linarith only [h1345, h2502, h2549, h2551, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h2419, h2551, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h1580, h2253, h2550, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h2252, h2254, h2549, h903, hlam]
              · linarith only [h2253, h2501, h903, hlam]
            · linarith only [h2252, h2500, h903, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2558 | h2558
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2559 | h2559
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2560 | h2560
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2561 | h2561
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2562 | h2562
              · linarith only [h2252, h2253, h2562, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2564 | h2564
                · linarith only [h2561, h2562, h2564, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2566 | h2566
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2567 | h2567
                    · linarith only [h2252, h2253, h2558, h2567, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2569 | h2569
                      · linarith only [h2559, h2564, h2569, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2571 | h2571
                        · linarith only [h1345, h2252, h2564, h2571, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi0]
                        · linarith only [h1580, h2252, h2558, h2562, h2571, hc45, hlam, hphi, u4ehi3]
                  · linarith only [h1580, h2252, h2566, hlam]
            · linarith only [h1580, h2252, h2558, h2561, hlam]
          · linarith only [h1580, h2252, h2558, h2560, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
        · linarith only [h1580, h2252, h2558, h2559, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2578 | h2578
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2579 | h2579
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2580 | h2580
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2581 | h2581
              · linarith only [h2252, h2253, h2581, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h2558, h2579, h2581, hlam]
            · linarith only [h1450, h2252, h2253, h2558, h2579, h2580, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2585 | h2585
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2586 | h2586
              · linarith only [h2252, h2253, h2586, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2588 | h2588
                · linarith only [h2558, h2578, h2586, h2588, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2590 | h2590
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2591 | h2591
                    · linarith only [h0, h2558, h2586, h2591, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h2558, h2578, h2590, h2591, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                  · linarith only [h2252, h2253, h2558, h2590, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · linarith only [h2252, h2585, h903, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2596 | h2596
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2597 | h2597
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2598 | h2598
              · linarith only [h2252, h2253, h2598, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h2558, h2596, h2598, hlam]
            · linarith only [h1450, h2252, h2253, h2558, h2596, h2597, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2602 | h2602
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2603 | h2603
              · linarith only [h2252, h2253, h2603, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2605 | h2605
                · linarith only [h2602, h2603, h2605, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2607 | h2607
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2608 | h2608
                    · linarith only [h2603, h2608, h903, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h2558, h2608, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h2252, h2558, h2607, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h2252, h2602, h903, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2613 | h2613
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2614 | h2614
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2615 | h2615
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2616 | h2616
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2617 | h2617
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2618 | h2618
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2619 | h2619
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2620 | h2620
                  · linarith only [h2252, h2613, h2614, h2620, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h1580, h2617, h2620, hc01, hc13, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2623 | h2623
                  · linarith only [h2252, h2613, h2614, h2623, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h1580, h2617, h2619, h2623, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h2252, h2613, h2617, h2618, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2627 | h2627
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2628 | h2628
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2629 | h2629
                  · linarith only [h2252, h2613, h2614, h2629, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2631 | h2631
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2632 | h2632
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2633 | h2633
                        · rcases h1bigk with h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c | h2634c
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [hlam, p2634_0]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h0, hlam, p2634_0]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h903, hlam, p2634_0]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h1345, hlam, p2634_0]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h1450, hlam, p2634_0]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            rcases p2634_3 (m.d 0 1) (by simp) with h2640 | h2640
                            · linarith only [h2640, hlam, p2634_0]
                            · rcases p2634_3 (m.d 1 2) (by simp) with h2642 | h2642
                              · rcases p2634_3 (m.d 1 3) (by simp) with h2643 | h2643
                                · linarith only [h2614, h2643, hlam]
                                · linarith only [h2643, h903, hlam]
                              · linarith only [h2642, hlam, p2634_0]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [hlam, p2634_0]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h1580, h2613, h2614, h2633, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2634_1, u4ehi4]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h1580, h2613, h2614, h2617, h2633, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2634_1, u4ehi4]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h1450, hc01, hc12, hlam, hphi, p2634_1]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h2617, hc01, hc34, hlam, hphi, ht12, ht23, p2634_1]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h2614, hlam, p2634_1]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [hlam, p2634_0]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h2617, hlam, p2634_1]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h1450, h2617, hc01, hc34, hlam, hphi, ht12, ht23, p2634_1]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            rcases p2634_3 (m.d 0 1) (by simp) with h2656 | h2656
                            · linarith only [h2656, hlam, p2634_0]
                            · rcases p2634_3 (m.d 1 2) (by simp) with h2658 | h2658
                              · rcases p2634_3 (m.d 1 3) (by simp) with h2659 | h2659
                                · linarith only [h2617, h2659, hlam]
                                · linarith only [h2659, h903, hlam]
                              · linarith only [h0, h2658, hlam]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h2615, hlam, p2634_1]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h1580, h2613, h2614, h2633, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2634_1, u4ehi4]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [hlam, p2634_0]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h1450, h2617, hc01, hc34, hlam, hphi, ht12, ht23, p2634_1]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h2617, h2627, hc01, hc34, hlam, hphi, ht12, ht23, p2634_1]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h2616, hlam, p2634_1]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h2627, hlam, p2634_0]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [h2628, hlam, p2634_0]
                          · have p2634_0 := h2634c.1
                            have p2634_1 := h2634c.2.1
                            have p2634_2 := h2634c.2.2.1
                            have p2634_3 := h2634c.2.2.2
                            linarith only [hlam, p2634_0]
                        · linarith only [h2617, h2633, h903, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h1580, h2628, h2629, h2632, hc01, hc14, hlam, hphi]
                    · linarith only [h1580, h2613, h2631, hlam]
                · linarith only [h2617, h2627, h2628, hlam]
              · linarith only [h1580, h2613, h2614, h2627, hlam]
          · linarith only [h0, h1580, h2614, h2616, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h1580, h2614, h2615, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2679 | h2679
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2680 | h2680
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2681 | h2681
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2682 | h2682
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2683 | h2683
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2684 | h2684
                  · linarith only [h2252, h2613, h2614, h2679, h2684, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h2614, h2679, h2684, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2687 | h2687
                  · linarith only [h2252, h2613, h2614, h2679, h2687, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h2614, h2681, h2683, h2687, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h2252, h2613, h2681, h2682, hlam]
            · linarith only [h2614, h2679, h2681, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2692 | h2692
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2693 | h2693
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2694 | h2694
                · linarith only [h2679, h2680, h2694, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2696 | h2696
                  · linarith only [h2252, h2613, h2614, h2679, h2696, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h2614, h2679, h2692, h2696, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h2252, h2613, h2679, h2680, h2692, h2693, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h2614, h2679, h2692, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2701 | h2701
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2702 | h2702
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2703 | h2703
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2704 | h2704
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2705 | h2705
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2706 | h2706
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2707 | h2707
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2708 | h2708
                        · linarith only [h2252, h2613, h2614, h2702, h2708, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h2252, h2613, h2704, h2708, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h2679, h2701, h2704, h2707, hlam]
                    · linarith only [h2252, h2613, h2614, h2702, h2706, hlam]
                  · linarith only [h2614, h2702, h2705, hlam]
                · linarith only [h2679, h2701, h2704, hlam]
              · linarith only [h2252, h2613, h2703, hc13, hc34, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2716 | h2716
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2717 | h2717
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2718 | h2718
                  · linarith only [h0, h2614, h2702, h2718, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h1450, h2614, h2701, h2718, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h2679, h2701, h2717, hlam]
              · linarith only [h2613, h2614, h2701, h2716, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2723 | h2723
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2724 | h2724
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2725 | h2725
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2726 | h2726
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2727 | h2727
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2728 | h2728
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2729 | h2729
                        · linarith only [h2252, h2613, h2614, h2723, h2729, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h2252, h2613, h2725, h2729, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h2679, h2725, h2728, hc01, hc15, hlam, hphi]
                    · linarith only [h2613, h2614, h2723, h2727, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi1]
                  · linarith only [h2614, h2723, h2726, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2735 | h2735
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2736 | h2736
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2737 | h2737
                      · linarith only [h2252, h2613, h2723, h2725, h2737, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h2679, h2737, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h2252, h2613, h2614, h2736, hc13, hc34, hlam, hphi]
                  · linarith only [h2614, h2723, h2725, h2735, h903, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h2252, h2613, h2723, h2724, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2743 | h2743
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2744 | h2744
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2745 | h2745
                  · linarith only [h0, h2701, h2723, h2743, h2745, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2614, h2745, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h2723, h2743, h2744, hlam]
              · linarith only [h2613, h2743, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2750 | h2750
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2751 | h2751
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2752 | h2752
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2753 | h2753
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2754 | h2754
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2755 | h2755
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2756 | h2756
                  · linarith only [h2252, h2750, h2756, h903, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h1580, h2750, h2753, h2756, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2759 | h2759
                  · linarith only [h0, h1580, h2252, h2750, h2759, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h1580, h2753, h2755, h2759, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h1580, h2252, h2753, h2754, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2763 | h2763
              · linarith only [h0, h1580, h2613, h2753, h2763, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2765 | h2765
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2766 | h2766
                  · linarith only [h2753, h2766, h903, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2768 | h2768
                    · linarith only [h2750, h2763, h2768, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2770 | h2770
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2771 | h2771
                        · rcases h1bigk with h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c | h2772c
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [hlam, p2772_0]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h0, hlam, p2772_0]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h903, hlam, p2772_0]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h1345, hlam, p2772_0]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h1450, hlam, p2772_0]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            rcases p2772_3 (m.d 0 1) (by simp) with h2778 | h2778
                            · linarith only [h2778, hlam, p2772_0]
                            · rcases p2772_3 (m.d 1 2) (by simp) with h2780 | h2780
                              · rcases p2772_3 (m.d 1 3) (by simp) with h2781 | h2781
                                · linarith only [h2750, h2781, hlam]
                                · linarith only [h2781, h903, hlam]
                              · linarith only [h2780, hlam, p2772_0]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [hlam, p2772_0]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h0, h1580, h2750, hc01, hc12, hlam, hphi, p2772_1]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h0, h1580, h2750, h2763, h2765, hc01, hc12, hlam, hphi, p2772_1]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h0, h1580, h2750, h2763, hc01, hc12, hlam, hphi, p2772_1]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h2763, h2771, hc01, hc34, hlam, hphi, ht12, ht23, p2772_1]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h2750, hlam, p2772_1]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [hlam, p2772_0]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h2753, hlam, p2772_1]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h2763, hlam, p2772_1]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            rcases p2772_3 (m.d 0 1) (by simp) with h2794 | h2794
                            · linarith only [h2794, hlam, p2772_0]
                            · rcases p2772_3 (m.d 1 2) (by simp) with h2796 | h2796
                              · rcases p2772_3 (m.d 1 3) (by simp) with h2797 | h2797
                                · linarith only [h2753, h2797, hlam]
                                · linarith only [h2797, h903, hlam]
                              · linarith only [h0, h2796, hlam]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h2751, hlam, p2772_1]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h903, hc01, hc14, hlam, hphi, p2772_1]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [hlam, p2772_0]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h0, h1580, h2750, h2753, h2763, hc01, hc34, hlam, hphi, ht12, ht23, p2772_1]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            rcases p2772_3 (m.d 0 1) (by simp) with h2805 | h2805
                            · linarith only [h2805, hlam, p2772_0]
                            · rcases p2772_3 (m.d 1 2) (by simp) with h2807 | h2807
                              · rcases p2772_3 (m.d 1 3) (by simp) with h2808 | h2808
                                · linarith only [h2763, h2808, hlam]
                                · linarith only [h2808, h903, hlam]
                              · linarith only [h0, h2807, hlam]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h2752, hlam, p2772_1]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h0, h1580, h2750, hc01, hc15, hlam, hphi, p2772_1]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [h2765, hlam, p2772_0]
                          · have p2772_0 := h2772c.1
                            have p2772_1 := h2772c.2.1
                            have p2772_2 := h2772c.2.2.1
                            have p2772_3 := h2772c.2.2.2
                            linarith only [hlam, p2772_0]
                        · linarith only [h0, h1580, h2750, h2753, h2771, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h1580, h2765, h2766, h2770, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2818 | h2818
                  · linarith only [h0, h1580, h2252, h2750, h2818, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2820 | h2820
                    · linarith only [h0, h1580, h2613, h2750, h2753, h2765, h2820, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2822 | h2822
                      · linarith only [h2753, h2765, h2822, h903, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2824 | h2824
                        · linarith only [h0, h1580, h2750, h2753, h2765, h2824, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h1580, h2750, h2753, h2824, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h1580, h2750, h2752, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h1580, h2750, h2751, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2829 | h2829
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2830 | h2830
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2831 | h2831
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2832 | h2832
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2833 | h2833
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2834 | h2834
                  · linarith only [h0, h1580, h2252, h2750, h2829, h2834, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h2750, h2829, h2834, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2837 | h2837
                  · linarith only [h0, h1580, h2252, h2750, h2829, h2837, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h2750, h2829, h2831, h2837, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h0, h1580, h2252, h2831, h2832, hc01, hc35, hlam, hphi, ht12, ht23]
            · linarith only [h2750, h2829, h2831, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2842 | h2842
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2843 | h2843
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2844 | h2844
                · linarith only [h2829, h2830, h2844, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2846 | h2846
                  · linarith only [h0, h1580, h2252, h2829, h2830, h2846, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h1580, h2842, h2846, hc01, hc13, hlam, hphi]
              · linarith only [h2252, h2842, h2843, hc03, hc35, hlam, hphi]
            · linarith only [h2750, h2829, h2842, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2851 | h2851
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2852 | h2852
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2853 | h2853
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2854 | h2854
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2855 | h2855
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2856 | h2856
                    · linarith only [h0, h1580, h2613, h2829, h2851, h2856, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h2829, h2855, h2856, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h1580, h2613, h2750, h2851, h2852, h2853, h2855, hc01, hc13, hlam, hphi]
                · linarith only [h2829, h2851, h2854, hlam]
              · linarith only [h0, h1580, h2252, h2852, h2853, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2862 | h2862
              · linarith only [h0, h1580, h2613, h2852, h2862, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h2750, h2851, h2862, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2865 | h2865
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2866 | h2866
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2867 | h2867
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2868 | h2868
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2869 | h2869
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2870 | h2870
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2871 | h2871
                        · rcases h1bigk with h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c | h2872c
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h0, hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h903, hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h1345, hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h1450, hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h2851, hc01, hc25, hlam, hphi, ht12, p2872_1]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h2750, hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h2829, hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h2851, hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            rcases p2872_3 (m.d 0 1) (by simp) with h2883 | h2883
                            · linarith only [h2883, hlam, p2872_0]
                            · rcases p2872_3 (m.d 1 2) (by simp) with h2885 | h2885
                              · linarith only [h2750, h2885, hlam]
                              · linarith only [h0, h2885, hlam]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h0, hc01, hc13, hlam, hphi, p2872_1]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h1345, h2750, hc01, hc23, hlam, hphi, ht12, p2872_1]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h0, h2750, h2851, hc01, hc23, hlam, hphi, ht12, p2872_1]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            rcases p2872_3 (m.d 0 1) (by simp) with h2892 | h2892
                            · linarith only [h2892, hlam, p2872_0]
                            · rcases p2872_3 (m.d 1 2) (by simp) with h2894 | h2894
                              · linarith only [h2829, h2894, hlam]
                              · linarith only [h0, h2894, hlam]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p2872_1]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h2865, hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h0, h1580, h2613, h2829, h2866, h2868, hc01, hc23, hlam, hphi, ht12, p2872_1]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            rcases p2872_3 (m.d 0 1) (by simp) with h2901 | h2901
                            · linarith only [h2901, hlam, p2872_0]
                            · rcases p2872_3 (m.d 1 2) (by simp) with h2903 | h2903
                              · linarith only [h2851, h2903, hlam]
                              · linarith only [h0, h2903, hlam]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p2872_1]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h2866, hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [h2867, hlam, p2872_0]
                          · have p2872_0 := h2872c.1
                            have p2872_1 := h2872c.2.1
                            have p2872_2 := h2872c.2.2.1
                            have p2872_3 := h2872c.2.2.2
                            linarith only [hlam, p2872_0]
                        · linarith only [h0, h1580, h2252, h2829, h2867, h2868, h2871, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h2829, h2867, h2870, hlam]
                    · linarith only [h0, h2750, h2869, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h2750, h2865, h2868, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2914 | h2914
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2915 | h2915
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2916 | h2916
                      · linarith only [h0, h1580, h2252, h2865, h2867, h2916, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h2829, h2916, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h2750, h2866, h2915, hlam]
                  · linarith only [h2750, h2865, h2914, hlam]
              · linarith only [h0, h1580, h2252, h2865, h2866, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2922 | h2922
              · linarith only [h0, h1580, h2613, h2865, h2922, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2924 | h2924
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2925 | h2925
                  · linarith only [h2865, h2925, h903, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2750, h2925, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2928 | h2928
                  · linarith only [h0, h2750, h2865, h2928, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h2750, h2928, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5862000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h903 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1345 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1450 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1580 | h1580
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h903 h1345 h1450 h1580
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h903 h1345 h1450 h1580

set_option maxHeartbeats 5862000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h903 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1345 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1450 | h1450
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h903 h1345 h1450
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h903 h1345 h1450

set_option maxHeartbeats 5862000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h903 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1345 | h1345
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h903 h1345
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h903 h1345

set_option maxHeartbeats 5862000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h903 | h903
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x0 m hb0 hb1 hb3 hb4 h0 h903
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1 m hb0 hb1 hb3 hb4 h0 h903

set_option maxHeartbeats 5862000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1 m hb0 hb1 hb3 hb4 h0

end R2N4
