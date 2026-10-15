import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1635 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1754 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1786 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h2241 | h2241
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2242 | h2242
    · linarith only [h0, h2242, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2244 | h2244
      · linarith only [h0, h1635, h2241, h2244, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2246 | h2246
        · linarith only [h0, h1754, h2246, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2248 | h2248
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2249 | h2249
            · linarith only [h1, h1786, h2249, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2251 | h2251
              · linarith only [h2248, h2249, h2251, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2253 | h2253
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2254 | h2254
                  · linarith only [h1, h1786, h2248, h2254, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h1635, h2241, h2244, h2251, h2253, h2254, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h2248, h2249, h2251, h2253, h4, hc02, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2258 | h2258
            · linarith only [h1, h1786, h2258, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2260 | h2260
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2261 | h2261
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2262 | h2262
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2263 | h2263
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2264 | h2264
                      · rcases h1bigk with h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c | h2265c
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          rcases p2265_3 (m.d 0 1) (by simp) with h2267 | h2267
                          · rcases p2265_3 (m.d 1 2) (by simp) with h2268 | h2268
                            · linarith only [h2268, hlam, p2265_0]
                            · rcases p2265_3 (m.d 1 3) (by simp) with h2270 | h2270
                              · linarith only [h1, h2270, hlam]
                              · linarith only [h2242, h2270, hlam]
                          · linarith only [h2267, hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          rcases p2265_3 (m.d 0 1) (by simp) with h2274 | h2274
                          · rcases p2265_3 (m.d 1 2) (by simp) with h2275 | h2275
                            · linarith only [h0, h2275, hlam]
                            · rcases p2265_3 (m.d 1 3) (by simp) with h2277 | h2277
                              · linarith only [h2277, hlam, p2265_0]
                              · rcases p2265_3 (m.d 1 4) (by simp) with h2279 | h2279
                                · linarith only [h2, h2279, hlam]
                                · linarith only [h2248, h2279, hlam]
                          · linarith only [h2274, hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h2260, hc01, hlam, hphi, ht0b, ht45, ht5b, p2265_1, u4ehi4]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          rcases p2265_3 (m.d 0 1) (by simp) with h2284 | h2284
                          · rcases p2265_3 (m.d 1 2) (by simp) with h2285 | h2285
                            · linarith only [h0, h2285, hlam]
                            · rcases p2265_3 (m.d 1 3) (by simp) with h2287 | h2287
                              · linarith only [h1, h2287, hlam]
                              · rcases p2265_3 (m.d 1 4) (by simp) with h2289 | h2289
                                · linarith only [h2, h2289, hlam]
                                · linarith only [h2260, h2289, hlam]
                          · linarith only [h2284, hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h0, hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h2242, hlam, p2265_1]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h2244, hlam, p2265_1]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h2246, hlam, p2265_1]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h1, hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h1, h1786, h2261, h2264, hc12, hc23, hlam, hphi, p2265_1]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h2248, hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h2258, hlam, p2265_1]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h2, hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h2248, h2261, hc12, hc23, hlam, hphi, p2265_1]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h2242, h2248, h2261, hc12, hc23, hlam, hphi, p2265_1]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h2248, h2261, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2265_1, u5ehi1]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h3, hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h1786, h2261, h2264, h3, hc12, hc23, hlam, hphi, p2265_1]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h1786, h2242, h2261, h2264, h3, hc12, hc23, hlam, hphi, p2265_1]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [h2260, hlam, p2265_0]
                        · have p2265_0 := h2265c.1
                          have p2265_1 := h2265c.2.1
                          have p2265_2 := h2265c.2.2.1
                          have p2265_3 := h2265c.2.2.2
                          linarith only [hlam, p2265_0]
                      · linarith only [h1635, h2241, h2242, h2248, h2264, hc12, hc24, hlam, hphi]
                    · linarith only [h1635, h2, h2260, h2263, hlam]
                  · linarith only [h2248, h2260, h2261, h2262, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2316 | h2316
                  · linarith only [h1, h1786, h2242, h2261, h2316, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2318 | h2318
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2319 | h2319
                      · rcases h1bigk with h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c | h2320c
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          rcases p2320_3 (m.d 0 1) (by simp) with h2322 | h2322
                          · rcases p2320_3 (m.d 1 2) (by simp) with h2323 | h2323
                            · linarith only [h2323, hlam, p2320_0]
                            · rcases p2320_3 (m.d 1 3) (by simp) with h2325 | h2325
                              · linarith only [h1, h2325, hlam]
                              · linarith only [h2242, h2325, hlam]
                          · linarith only [h2322, hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          rcases p2320_3 (m.d 0 1) (by simp) with h2329 | h2329
                          · rcases p2320_3 (m.d 1 2) (by simp) with h2330 | h2330
                            · linarith only [h0, h2330, hlam]
                            · rcases p2320_3 (m.d 1 3) (by simp) with h2332 | h2332
                              · linarith only [h2332, hlam, p2320_0]
                              · rcases p2320_3 (m.d 1 4) (by simp) with h2334 | h2334
                                · linarith only [h2, h2334, hlam]
                                · linarith only [h2248, h2334, hlam]
                          · linarith only [h2329, hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h2260, hc01, hlam, hphi, ht0b, ht45, ht5b, p2320_1, u4ehi4]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          rcases p2320_3 (m.d 0 1) (by simp) with h2339 | h2339
                          · rcases p2320_3 (m.d 1 2) (by simp) with h2340 | h2340
                            · linarith only [h0, h2340, hlam]
                            · rcases p2320_3 (m.d 1 3) (by simp) with h2342 | h2342
                              · linarith only [h1, h2342, hlam]
                              · rcases p2320_3 (m.d 1 4) (by simp) with h2344 | h2344
                                · linarith only [h2, h2344, hlam]
                                · linarith only [h2260, h2344, hlam]
                          · linarith only [h2339, hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h0, hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h2242, hlam, p2320_1]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h2244, hlam, p2320_1]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h2246, hlam, p2320_1]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h1, hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h1, h2316, h2319, h4, hc12, hc34, hlam, hphi, ht23, p2320_1]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h2248, hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h2258, hlam, p2320_1]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h2, hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          rcases p2320_3 (m.d 0 1) (by simp) with h2359 | h2359
                          · rcases p2320_3 (m.d 1 2) (by simp) with h2360 | h2360
                            · linarith only [h2244, h2360, hlam]
                            · rcases p2320_3 (m.d 1 3) (by simp) with h2362 | h2362
                              · linarith only [h2248, h2362, hlam]
                              · linarith only [h2242, h2362, hlam]
                          · linarith only [h0, h2359, hlam]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          rcases p2320_3 (m.d 0 1) (by simp) with h2366 | h2366
                          · rcases p2320_3 (m.d 1 2) (by simp) with h2367 | h2367
                            · linarith only [h2244, h2367, hlam]
                            · rcases p2320_3 (m.d 1 3) (by simp) with h2369 | h2369
                              · linarith only [h2248, h2369, hlam]
                              · rcases p2320_3 (m.d 1 4) (by simp) with h2371 | h2371
                                · rcases p2320_3 (m.d 1 5) (by simp) with h2372 | h2372
                                  · linarith only [h2260, h2372, hlam]
                                  · linarith only [h2258, h2372, hlam]
                                · linarith only [h2248, h2371, hlam]
                          · linarith only [h1, h2366, hlam]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h2, h2260, hc01, hlam, hphi, ht0b, ht45, ht5b, p2320_1, u4ehi4]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h3, hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          rcases p2320_3 (m.d 0 1) (by simp) with h2380 | h2380
                          · rcases p2320_3 (m.d 1 2) (by simp) with h2381 | h2381
                            · linarith only [h2246, h2381, hlam]
                            · rcases p2320_3 (m.d 1 3) (by simp) with h2383 | h2383
                              · linarith only [h2258, h2383, hlam]
                              · linarith only [h2242, h2383, hlam]
                          · linarith only [h0, h2380, hlam]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          rcases p2320_3 (m.d 0 1) (by simp) with h2387 | h2387
                          · rcases p2320_3 (m.d 1 2) (by simp) with h2388 | h2388
                            · linarith only [h2246, h2388, hlam]
                            · rcases p2320_3 (m.d 1 3) (by simp) with h2390 | h2390
                              · linarith only [h2258, h2390, hlam]
                              · rcases p2320_3 (m.d 1 4) (by simp) with h2392 | h2392
                                · rcases p2320_3 (m.d 1 5) (by simp) with h2393 | h2393
                                  · rcases h2bigk with h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c | h2394c
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2316, h2319, h4, hc12, hc34, hlam, hphi, ht23, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h4, hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h1635, hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h1754, hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h0, hlam, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2242, hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2244, hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2246, hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2316, h2319, hc02, hc34, hlam, hphi, ht23, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2316, h2319, hc12, hc34, hlam, hphi, ht23, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2261, hlam, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2316, hlam, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      rcases p2394_3 (m.d 0 2) (by simp) with h2410 | h2410
                                      · linarith only [h2410, hlam, p2394_0]
                                      · rcases p2394_3 (m.d 1 2) (by simp) with h2412 | h2412
                                        · linarith only [h2244, h2412, hlam]
                                        · rcases p2394_3 (m.d 2 3) (by simp) with h2414 | h2414
                                          · linarith only [h2261, h2414, hlam]
                                          · linarith only [h2414, h4, hlam]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      rcases p2394_3 (m.d 0 2) (by simp) with h2417 | h2417
                                      · linarith only [h1635, h2417, hlam]
                                      · linarith only [h0, h2417, hlam]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h0, h4, hc12, hc24, hlam, hphi, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [hlam, p2394_0]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h1754, h2242, h2261, h3, hc12, hc34, hlam, hphi, ht23, p2320_1, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      rcases p2394_3 (m.d 0 2) (by simp) with h2423 | h2423
                                      · linarith only [h2423, hlam, p2394_0]
                                      · rcases p2394_3 (m.d 1 2) (by simp) with h2425 | h2425
                                        · linarith only [h2246, h2425, hlam]
                                        · rcases p2394_3 (m.d 2 3) (by simp) with h2427 | h2427
                                          · linarith only [h2316, h2427, hlam]
                                          · linarith only [h2427, h4, hlam]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      rcases p2394_3 (m.d 0 2) (by simp) with h2430 | h2430
                                      · linarith only [h1754, h2430, hlam]
                                      · linarith only [h0, h2430, hlam]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [h2318, hlam, p2394_1]
                                    · have p2394_0 := h2394c.1
                                      have p2394_1 := h2394c.2.1
                                      have p2394_2 := h2394c.2.2.1
                                      have p2394_3 := h2394c.2.2.2
                                      linarith only [hlam, p2394_0]
                                  · linarith only [h2258, h2393, hlam]
                                · linarith only [h2248, h2392, hlam]
                          · linarith only [h1, h2387, hlam]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [h2260, hlam, p2320_0]
                        · have p2320_0 := h2320c.1
                          have p2320_1 := h2320c.2.1
                          have p2320_2 := h2320c.2.2.1
                          have p2320_3 := h2320c.2.2.2
                          linarith only [hlam, p2320_0]
                      · linarith only [h1635, h2241, h2261, h2319, hlam]
                    · linarith only [h1635, h2, h2260, h2318, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2443 | h2443
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2444 | h2444
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2445 | h2445
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2446 | h2446
                      · linarith only [h2260, h2443, h2446, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                      · linarith only [h1635, h2241, h2242, h2248, h2443, h2446, hc12, hc23, hlam, hphi]
                    · linarith only [h1635, h2241, h2445, hlam]
                  · linarith only [h1635, h2241, h2260, h2443, h2444, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2451 | h2451
                  · linarith only [h1786, h2443, h2451, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2453 | h2453
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2454 | h2454
                      · rcases h1bigk with h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c | h2455c
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          rcases p2455_3 (m.d 0 1) (by simp) with h2457 | h2457
                          · rcases p2455_3 (m.d 1 2) (by simp) with h2458 | h2458
                            · linarith only [h2458, hlam, p2455_0]
                            · rcases p2455_3 (m.d 1 3) (by simp) with h2460 | h2460
                              · linarith only [h1, h2460, hlam]
                              · linarith only [h2242, h2460, hlam]
                          · linarith only [h2457, hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          rcases p2455_3 (m.d 0 1) (by simp) with h2464 | h2464
                          · rcases p2455_3 (m.d 1 2) (by simp) with h2465 | h2465
                            · linarith only [h0, h2465, hlam]
                            · rcases p2455_3 (m.d 1 3) (by simp) with h2467 | h2467
                              · linarith only [h2467, hlam, p2455_0]
                              · rcases p2455_3 (m.d 1 4) (by simp) with h2469 | h2469
                                · linarith only [h2, h2469, hlam]
                                · linarith only [h2248, h2469, hlam]
                          · linarith only [h2464, hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          rcases p2455_3 (m.d 0 1) (by simp) with h2473 | h2473
                          · rcases p2455_3 (m.d 1 2) (by simp) with h2474 | h2474
                            · linarith only [h0, h2474, hlam]
                            · rcases p2455_3 (m.d 1 3) (by simp) with h2476 | h2476
                              · linarith only [h1, h2476, hlam]
                              · rcases p2455_3 (m.d 1 4) (by simp) with h2478 | h2478
                                · linarith only [h2478, hlam, p2455_0]
                                · rcases p2455_3 (m.d 1 5) (by simp) with h2480 | h2480
                                  · linarith only [h2480, h3, hlam]
                                  · linarith only [h2260, h2480, hlam]
                          · linarith only [h2473, hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          rcases p2455_3 (m.d 0 1) (by simp) with h2484 | h2484
                          · rcases p2455_3 (m.d 1 2) (by simp) with h2485 | h2485
                            · linarith only [h0, h2485, hlam]
                            · rcases p2455_3 (m.d 1 3) (by simp) with h2487 | h2487
                              · linarith only [h1, h2487, hlam]
                              · rcases p2455_3 (m.d 1 4) (by simp) with h2489 | h2489
                                · linarith only [h2, h2489, hlam]
                                · rcases p2455_3 (m.d 1 5) (by simp) with h2491 | h2491
                                  · linarith only [h2491, hlam, p2455_0]
                                  · rcases h2bigk with h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c | h2493c
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [hlam, p2493_0]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h2451, h2454, h4, hc12, hc34, hlam, hphi, ht23, p2493_1]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h4, hlam, p2493_0]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h1635, hlam, p2493_0]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h1754, hlam, p2493_0]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h0, hlam, p2493_1]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [hlam, p2493_0]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h2242, hlam, p2493_0]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h2244, hlam, p2493_0]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h2246, hlam, p2493_0]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h2451, h2454, hc02, hc34, hlam, hphi, ht23, p2493_1]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h2451, h2454, hc12, hc34, hlam, hphi, ht23, p2493_1]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [hlam, p2493_0]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h2443, hlam, p2493_1]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h2451, hlam, p2493_1]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      rcases p2493_3 (m.d 0 2) (by simp) with h2509 | h2509
                                      · linarith only [h2509, hlam, p2493_0]
                                      · rcases p2493_3 (m.d 1 2) (by simp) with h2511 | h2511
                                        · linarith only [h2244, h2511, hlam]
                                        · rcases p2493_3 (m.d 2 3) (by simp) with h2513 | h2513
                                          · linarith only [h2443, h2513, hlam]
                                          · linarith only [h2513, h4, hlam]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      rcases p2493_3 (m.d 0 2) (by simp) with h2516 | h2516
                                      · linarith only [h1635, h2516, hlam]
                                      · linarith only [h0, h2516, hlam]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h0, h4, hc12, hc24, hlam, hphi, p2493_1]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [hlam, p2493_0]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h0, h1754, hc12, hc24, hlam, hphi, p2493_1]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      rcases p2493_3 (m.d 0 2) (by simp) with h2522 | h2522
                                      · linarith only [h2522, hlam, p2493_0]
                                      · rcases p2493_3 (m.d 1 2) (by simp) with h2524 | h2524
                                        · linarith only [h2246, h2524, hlam]
                                        · rcases p2493_3 (m.d 2 3) (by simp) with h2526 | h2526
                                          · linarith only [h2451, h2526, hlam]
                                          · linarith only [h2526, h4, hlam]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      rcases p2493_3 (m.d 0 2) (by simp) with h2529 | h2529
                                      · linarith only [h1754, h2529, hlam]
                                      · linarith only [h0, h2529, hlam]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p2493_1]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [h2453, hlam, p2493_1]
                                    · have p2493_0 := h2493c.1
                                      have p2493_1 := h2493c.2.1
                                      have p2493_2 := h2493c.2.2.1
                                      have p2493_3 := h2493c.2.2.2
                                      linarith only [hlam, p2493_0]
                          · linarith only [h2484, hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h0, hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h2242, hlam, p2455_1]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h2244, hlam, p2455_1]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h2246, hlam, p2455_1]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h1, hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h2241, h2248, h2260, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2455_1]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h2248, hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h2258, hlam, p2455_1]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h2, hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h1635, h2241, h2260, h2443, hc12, hc34, hlam, hphi, ht23, p2455_1]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h1635, h2241, h2260, h2443, hc13, hc34, hlam, hphi, p2455_1]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h2260, hlam, p2455_1]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h3, hlam, p2455_0]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h1635, h2241, h2260, h2443, hc12, hc34, hlam, hphi, ht23, p2455_1]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h1635, h2241, h2242, h2260, h2443, hc12, hc34, hlam, hphi, ht23, p2455_1]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [h1635, h2241, h2260, h2443, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2455_1, u4ehi1]
                        · have p2455_0 := h2455c.1
                          have p2455_1 := h2455c.2.1
                          have p2455_2 := h2455c.2.2.1
                          have p2455_3 := h2455c.2.2.2
                          linarith only [hlam, p2455_0]
                      · linarith only [h1635, h2241, h2443, h2454, hlam]
                    · linarith only [h1635, h2241, h2453, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2558 | h2558
    · linarith only [h0, h2558, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2560 | h2560
      · linarith only [h0, h1635, h2560, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2562 | h2562
        · linarith only [h0, h1754, h2562, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2564 | h2564
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2565 | h2565
            · linarith only [h1, h1786, h2565, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2567 | h2567
              · linarith only [h2, h2241, h2567, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2569 | h2569
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2570 | h2570
                  · linarith only [h1, h1786, h2564, h2570, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2572 | h2572
                    · linarith only [h2241, h2569, h2570, h2572, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2574 | h2574
                      · linarith only [h1, h2564, h2572, h2574, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h1, h2564, h2570, h2574, h4, hc45, hlam, hphi, u4ehi3]
                · linarith only [h1, h2564, h2569, h4, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2578 | h2578
            · linarith only [h1, h1786, h2578, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2580 | h2580
              · linarith only [h2, h2241, h2580, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2582 | h2582
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2583 | h2583
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2584 | h2584
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2585 | h2585
                      · linarith only [h2241, h2582, h2585, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · linarith only [h2558, h2564, h2582, h2584, h2585, hc12, hc23, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2588 | h2588
                      · linarith only [h0, h1635, h2584, h2588, hc12, hc34, hlam, hphi, ht23]
                      · rcases h1bigk with h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c | h2590c
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          rcases p2590_3 (m.d 0 1) (by simp) with h2592 | h2592
                          · rcases p2590_3 (m.d 1 2) (by simp) with h2593 | h2593
                            · linarith only [h2593, hlam, p2590_0]
                            · rcases p2590_3 (m.d 1 3) (by simp) with h2595 | h2595
                              · linarith only [h1, h2595, hlam]
                              · linarith only [h2558, h2595, hlam]
                          · linarith only [h2592, hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          rcases p2590_3 (m.d 0 1) (by simp) with h2599 | h2599
                          · rcases p2590_3 (m.d 1 2) (by simp) with h2600 | h2600
                            · linarith only [h0, h2600, hlam]
                            · rcases p2590_3 (m.d 1 3) (by simp) with h2602 | h2602
                              · linarith only [h2602, hlam, p2590_0]
                              · rcases p2590_3 (m.d 1 4) (by simp) with h2604 | h2604
                                · linarith only [h2, h2604, hlam]
                                · linarith only [h2564, h2604, hlam]
                          · linarith only [h2599, hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          rcases p2590_3 (m.d 0 1) (by simp) with h2608 | h2608
                          · rcases p2590_3 (m.d 1 2) (by simp) with h2609 | h2609
                            · linarith only [h0, h2609, hlam]
                            · rcases p2590_3 (m.d 1 3) (by simp) with h2611 | h2611
                              · linarith only [h1, h2611, hlam]
                              · rcases p2590_3 (m.d 1 4) (by simp) with h2613 | h2613
                                · linarith only [h2613, hlam, p2590_0]
                                · rcases p2590_3 (m.d 1 5) (by simp) with h2615 | h2615
                                  · linarith only [h2615, h3, hlam]
                                  · linarith only [h2580, h2615, hlam]
                          · linarith only [h2608, hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          rcases p2590_3 (m.d 0 1) (by simp) with h2619 | h2619
                          · rcases p2590_3 (m.d 1 2) (by simp) with h2620 | h2620
                            · linarith only [h0, h2620, hlam]
                            · rcases p2590_3 (m.d 1 3) (by simp) with h2622 | h2622
                              · linarith only [h1, h2622, hlam]
                              · rcases p2590_3 (m.d 1 4) (by simp) with h2624 | h2624
                                · linarith only [h2, h2624, hlam]
                                · rcases p2590_3 (m.d 1 5) (by simp) with h2626 | h2626
                                  · linarith only [h2626, hlam, p2590_0]
                                  · rcases h2bigk with h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c | h2628c
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p2628_1]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h4, hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h1635, hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h1754, hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h0, hlam, p2628_1]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h2558, hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h2560, hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h2562, hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      rcases p2628_3 (m.d 0 2) (by simp) with h2639 | h2639
                                      · linarith only [h2639, hlam, p2628_0]
                                      · rcases p2628_3 (m.d 1 2) (by simp) with h2641 | h2641
                                        · linarith only [h2558, h2641, hlam]
                                        · rcases p2628_3 (m.d 2 3) (by simp) with h2643 | h2643
                                          · rcases p2628_3 (m.d 2 4) (by simp) with h2644 | h2644
                                            · linarith only [h2582, h2644, hlam]
                                            · linarith only [h1635, h2644, hlam]
                                          · linarith only [h2643, hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      rcases p2628_3 (m.d 0 2) (by simp) with h2648 | h2648
                                      · linarith only [h2648, h4, hlam]
                                      · linarith only [h0, h2648, hlam]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h2558, h2564, h2582, hc12, hc23, hlam, hphi, p2628_1]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h1754, hc02, hc23, hlam, hphi, p2628_1]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h0, h2584, hc12, hc45, hlam, hphi, ht23, ht34, p2628_1]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h2584, hc12, hc45, hlam, hphi, ht23, ht34, p2628_1]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h2582, hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h2584, hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      rcases p2628_3 (m.d 0 2) (by simp) with h2659 | h2659
                                      · linarith only [h2659, hlam, p2628_0]
                                      · rcases p2628_3 (m.d 1 2) (by simp) with h2661 | h2661
                                        · linarith only [h2562, h2661, hlam]
                                        · rcases p2628_3 (m.d 2 3) (by simp) with h2663 | h2663
                                          · rcases p2628_3 (m.d 2 4) (by simp) with h2664 | h2664
                                            · linarith only [h2584, h2664, hlam]
                                            · linarith only [h1635, h2664, hlam]
                                          · linarith only [h2663, h4, hlam]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      rcases p2628_3 (m.d 0 2) (by simp) with h2668 | h2668
                                      · linarith only [h1754, h2668, hlam]
                                      · linarith only [h0, h2668, hlam]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h2583, hlam, p2628_0]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [h0, h1635, hc12, hc25, hlam, hphi, p2628_1]
                                    · have p2628_0 := h2628c.1
                                      have p2628_1 := h2628c.2.1
                                      have p2628_2 := h2628c.2.2.1
                                      have p2628_3 := h2628c.2.2.2
                                      linarith only [hlam, p2628_0]
                          · linarith only [h2619, hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h0, hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h2558, hlam, p2590_1]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h2560, hlam, p2590_1]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h2562, hlam, p2590_1]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h1, hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h2564, hc12, hc34, hlam, hphi, ht23, p2590_1]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h2564, hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h2578, hlam, p2590_1]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h2, hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h2, h2241, hc12, hc45, hlam, hphi, ht23, ht34, p2590_1]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h2, h2241, hc13, hc45, hlam, hphi, ht34, p2590_1]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h2580, hlam, p2590_1]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h3, hlam, p2590_0]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h1786, h2583, h3, hc12, hc23, hlam, hphi, p2590_1]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h1786, h2558, h2583, h3, hc12, hc23, hlam, hphi, p2590_1]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [h1786, h2583, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2590_1, u4ehi1]
                        · have p2590_0 := h2590c.1
                          have p2590_1 := h2590c.2.1
                          have p2590_2 := h2590c.2.2.1
                          have p2590_3 := h2590c.2.2.2
                          linarith only [hlam, p2590_0]
                  · linarith only [h2564, h2582, h2583, hc13, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2696 | h2696
                  · linarith only [h1786, h2582, h2696, h4, hc02, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2698 | h2698
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2699 | h2699
                      · rcases h1bigk with h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c | h2700c
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          rcases p2700_3 (m.d 0 1) (by simp) with h2702 | h2702
                          · rcases p2700_3 (m.d 1 2) (by simp) with h2703 | h2703
                            · linarith only [h2703, hlam, p2700_0]
                            · rcases p2700_3 (m.d 1 3) (by simp) with h2705 | h2705
                              · linarith only [h1, h2705, hlam]
                              · linarith only [h2558, h2705, hlam]
                          · linarith only [h2702, hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          rcases p2700_3 (m.d 0 1) (by simp) with h2709 | h2709
                          · rcases p2700_3 (m.d 1 2) (by simp) with h2710 | h2710
                            · linarith only [h0, h2710, hlam]
                            · rcases p2700_3 (m.d 1 3) (by simp) with h2712 | h2712
                              · linarith only [h2712, hlam, p2700_0]
                              · rcases p2700_3 (m.d 1 4) (by simp) with h2714 | h2714
                                · linarith only [h2, h2714, hlam]
                                · linarith only [h2564, h2714, hlam]
                          · linarith only [h2709, hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          rcases p2700_3 (m.d 0 1) (by simp) with h2718 | h2718
                          · rcases p2700_3 (m.d 1 2) (by simp) with h2719 | h2719
                            · linarith only [h0, h2719, hlam]
                            · rcases p2700_3 (m.d 1 3) (by simp) with h2721 | h2721
                              · linarith only [h1, h2721, hlam]
                              · rcases p2700_3 (m.d 1 4) (by simp) with h2723 | h2723
                                · linarith only [h2723, hlam, p2700_0]
                                · rcases p2700_3 (m.d 1 5) (by simp) with h2725 | h2725
                                  · linarith only [h2725, h3, hlam]
                                  · linarith only [h2580, h2725, hlam]
                          · linarith only [h2718, hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          rcases p2700_3 (m.d 0 1) (by simp) with h2729 | h2729
                          · rcases p2700_3 (m.d 1 2) (by simp) with h2730 | h2730
                            · linarith only [h0, h2730, hlam]
                            · rcases p2700_3 (m.d 1 3) (by simp) with h2732 | h2732
                              · linarith only [h1, h2732, hlam]
                              · rcases p2700_3 (m.d 1 4) (by simp) with h2734 | h2734
                                · linarith only [h2, h2734, hlam]
                                · rcases p2700_3 (m.d 1 5) (by simp) with h2736 | h2736
                                  · linarith only [h2736, hlam, p2700_0]
                                  · rcases h2bigk with h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c | h2738c
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [hlam, p2738_0]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h2696, h2699, h4, hc12, hc34, hlam, hphi, ht23, p2738_1]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h4, hlam, p2738_0]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h1635, hlam, p2738_0]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h1754, hlam, p2738_0]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h0, hlam, p2738_1]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [hlam, p2738_0]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h2558, hlam, p2738_0]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h2560, hlam, p2738_0]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h2562, hlam, p2738_0]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h2696, h2699, hc02, hc34, hlam, hphi, ht23, p2738_1]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h2696, h2699, hc12, hc34, hlam, hphi, ht23, p2738_1]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [hlam, p2738_0]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h2582, hlam, p2738_1]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h2696, hlam, p2738_1]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      rcases p2738_3 (m.d 0 2) (by simp) with h2754 | h2754
                                      · linarith only [h2754, hlam, p2738_0]
                                      · rcases p2738_3 (m.d 1 2) (by simp) with h2756 | h2756
                                        · linarith only [h2560, h2756, hlam]
                                        · rcases p2738_3 (m.d 2 3) (by simp) with h2758 | h2758
                                          · linarith only [h2582, h2758, hlam]
                                          · linarith only [h2758, h4, hlam]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      rcases p2738_3 (m.d 0 2) (by simp) with h2761 | h2761
                                      · linarith only [h1635, h2761, hlam]
                                      · linarith only [h0, h2761, hlam]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h0, h2582, h4, hc12, hc34, hlam, hphi, ht23, p2738_1]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [hlam, p2738_0]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h0, h1754, h2582, hc12, hc34, hlam, hphi, ht23, p2738_1]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      rcases p2738_3 (m.d 0 2) (by simp) with h2767 | h2767
                                      · linarith only [h2767, hlam, p2738_0]
                                      · rcases p2738_3 (m.d 1 2) (by simp) with h2769 | h2769
                                        · linarith only [h2562, h2769, hlam]
                                        · rcases p2738_3 (m.d 2 3) (by simp) with h2771 | h2771
                                          · linarith only [h2696, h2771, hlam]
                                          · linarith only [h2771, h4, hlam]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      rcases p2738_3 (m.d 0 2) (by simp) with h2774 | h2774
                                      · linarith only [h1754, h2774, hlam]
                                      · linarith only [h0, h2774, hlam]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p2738_1]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [h2698, hlam, p2738_1]
                                    · have p2738_0 := h2738c.1
                                      have p2738_1 := h2738c.2.1
                                      have p2738_2 := h2738c.2.2.1
                                      have p2738_3 := h2738c.2.2.2
                                      linarith only [hlam, p2738_0]
                          · linarith only [h2729, hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h0, hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h2558, hlam, p2700_1]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h2560, hlam, p2700_1]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h2562, hlam, p2700_1]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h1, hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h1, h1786, h2699, hc12, hc34, hlam, hphi, ht23, p2700_1]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h2564, hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h2578, hlam, p2700_1]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h2, hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h2, h2241, h2582, h2698, hc12, hc34, hlam, hphi, ht23, p2700_1]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h2, h2241, h2582, h2698, hc13, hc34, hlam, hphi, p2700_1]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h2580, hlam, p2700_1]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h3, hlam, p2700_0]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h2241, h2582, h2698, h3, hc12, hc34, hlam, hphi, ht23, p2700_1]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h2241, h2558, h2582, h2698, h3, hc12, hc34, hlam, hphi, ht23, p2700_1]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [h2241, h2582, h2698, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2700_1, u4ehi1]
                        · have p2700_0 := h2700c.1
                          have p2700_1 := h2700c.2.1
                          have p2700_2 := h2700c.2.2.1
                          have p2700_3 := h2700c.2.2.2
                          linarith only [hlam, p2700_0]
                      · linarith only [h2582, h2698, h2699, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2802 | h2802
                      · linarith only [h0, h2582, h2698, h2802, h4, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h2582, h2802, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1635 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1754 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h1786 | h1786
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h1635 h1754 h1786
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h1635 h1754 h1786

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1635 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1754 | h1754
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h1635 h1754
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h1635 h1754

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h1635 | h1635
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h1635
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h1635

set_option maxHeartbeats 5602000 in
set_option maxHeartbeats 5602000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 5726000 in
set_option maxHeartbeats 5726000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s3 m hb1 hb2 hb4 hb5 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2805 | h2805
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2806 | h2806
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2807 | h2807
        · linarith only [h0, h2807, h3, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2809 | h2809
          · linarith only [h1, h2809, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2811 | h2811
            · linarith only [h0, h2806, h2811, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2813 | h2813
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2814 | h2814
                · linarith only [h0, h2814, h3, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h2806, h2807, h2814, hc12, hc25, hlam, hphi]
              · linarith only [h2805, h2807, h2813, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2818 | h2818
        · linarith only [h0, h2818, h3, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2820 | h2820
          · linarith only [h2, h2805, h2806, h2820, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2822 | h2822
            · linarith only [h2, h2822, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2824 | h2824
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2825 | h2825
                · linarith only [h0, h2806, h2825, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2827 | h2827
                  · linarith only [h0, h2827, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2829 | h2829
                    · linarith only [h1, h2827, h2829, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2831 | h2831
                      · linarith only [h2, h2824, h2825, h2827, h2831, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h2, h2824, h2825, h2831, h3, hc23, hc35, hlam, hphi]
              · linarith only [h2805, h2806, h2822, h2824, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2835 | h2835
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2836 | h2836
        · linarith only [h0, h2836, h3, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2838 | h2838
          · linarith only [h1, h2838, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2840 | h2840
            · linarith only [h1, h2805, h2835, h2840, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2842 | h2842
              · linarith only [h2805, h2835, h2842, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2844 | h2844
                · linarith only [h1, h2842, h2844, h3, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h2805, h2835, h2844, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2847 | h2847
        · linarith only [h0, h2847, h3, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2849 | h2849
          · linarith only [h1, h2849, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2851 | h2851
            · linarith only [h2, h2851, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2853 | h2853
              · linarith only [h0, h2805, h2853, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2855 | h2855
                · linarith only [h1, h2835, h2853, h2855, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2857 | h2857
                  · linarith only [h0, h2847, h2857, h3, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2859 | h2859
                    · linarith only [h1, h2857, h2859, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2861 | h2861
                      · linarith only [h2, h2849, h2857, h2859, h2861, h3, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2863 | h2863
                        · linarith only [h2, h2835, h2851, h2861, h2863, h3, hc02, hc35, hlam, hphi, ht23]
                        · linarith only [h2, h2863, h3, hc45, hlam, hphi, u4ehi1]

set_option maxHeartbeats 6154000 in
set_option maxHeartbeats 6154000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s2 m hb1 hb2 hb4 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2866 | h2866
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2867 | h2867
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2868 | h2868
        · linarith only [h0, h2, h2868, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2870 | h2870
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2871 | h2871
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2872 | h2872
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2873 | h2873
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2874 | h2874
                  · linarith only [h2868, h2870, h2874, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2876 | h2876
                    · linarith only [h0, h2, h2874, h2876, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · linarith only [h0, h2, h2870, h2874, h2876, hc12, hc24, hlam, hphi]
                · linarith only [h2867, h2868, h2873, hc12, hc24, hlam, hphi]
              · linarith only [h1, h2, h2871, h2872, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2881 | h2881
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2882 | h2882
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2883 | h2883
                  · linarith only [h2868, h2870, h2883, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2885 | h2885
                    · linarith only [h0, h2, h2885, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h0, h2, h2870, h2883, h2885, hc12, hc24, hlam, hphi]
                · linarith only [h2867, h2868, h2882, hc12, hc24, hlam, hphi]
              · linarith only [h0, h2, h2870, h2881, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2890 | h2890
            · linarith only [h2867, h2870, h2890, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2892 | h2892
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2893 | h2893
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2894 | h2894
                  · linarith only [h0, h2, h2894, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2896 | h2896
                    · linarith only [h0, h2, h2870, h2894, h2896, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2898 | h2898
                      · linarith only [h1, h2, h2894, h2898, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h2, h2866, h2893, h2896, h2898, hc23, hc34, hlam, hphi]
                · linarith only [h2867, h2870, h2893, hc12, hc25, hlam, hphi]
              · linarith only [h2, h2866, h2892, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2903 | h2903
        · linarith only [h1, h2, h2867, h2903, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2905 | h2905
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2906 | h2906
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2907 | h2907
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2908 | h2908
                · linarith only [h2867, h2905, h2908, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2910 | h2910
                  · linarith only [h2903, h2905, h2910, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2912 | h2912
                    · linarith only [h1, h2, h2908, h2912, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h2867, h2905, h2912, hc12, hc23, hlam, hphi]
              · linarith only [h2, h2866, h2907, hlam]
            · linarith only [h2867, h2905, h2906, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2917 | h2917
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2918 | h2918
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2919 | h2919
                · linarith only [h0, h2, h2867, h2919, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2921 | h2921
                  · linarith only [h0, h2, h2903, h2921, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2923 | h2923
                    · linarith only [h1, h2, h2905, h2919, h2921, h2923, hc02, hc24, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2925 | h2925
                      · linarith only [h1, h2, h2921, h2925, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2927 | h2927
                        · linarith only [h1, h2, h2925, h2927, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h1, h2, h2917, h2925, h2927, hc13, hc34, hlam, hphi]
              · linarith only [h2, h2866, h2918, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2931 | h2931
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2932 | h2932
                · linarith only [h0, h2867, h2932, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2934 | h2934
                  · linarith only [h0, h2, h2934, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2936 | h2936
                    · linarith only [h1, h2, h2905, h2932, h2934, h2936, hc02, hc24, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2938 | h2938
                      · linarith only [h1, h2, h2934, h2938, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2940 | h2940
                        · linarith only [h1, h2, h2938, h2940, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2942 | h2942
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2943 | h2943
                            · linarith only [h2, h2866, h2938, h2943, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2945 | h2945
                              · linarith only [h2917, h2943, h2945, hc03, hc34, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2947 | h2947
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2948 | h2948
                                  · rcases h1bigk with h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c | h2949c
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [hlam, p2949_0]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2, h2934, h2943, hc12, hc34, hlam, hphi, ht23, p2949_1]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2, h2932, h2934, h2943, hc12, hc34, hlam, hphi, ht23, p2949_1]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2, hlam, p2949_0]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2, h2942, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2949_1, u4ehi4]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h0, hlam, p2949_0]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [hlam, p2949_0]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2932, hlam, p2949_1]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2934, hlam, p2949_1]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2936, hlam, p2949_1]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h1, hlam, p2949_0]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2949_1]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [hlam, p2949_0]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2938, hlam, p2949_0]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2940, hlam, p2949_1]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2866, h2942, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2949_1, u4ehi4]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      rcases p2949_3 (m.d 0 1) (by simp) with h2966 | h2966
                                      · linarith only [h2, h2966, hlam]
                                      · linarith only [h0, h2966, hlam]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      rcases p2949_3 (m.d 0 1) (by simp) with h2969 | h2969
                                      · linarith only [h2, h2969, hlam]
                                      · linarith only [h1, h2969, hlam]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [hlam, p2949_0]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      rcases p2949_3 (m.d 0 1) (by simp) with h2973 | h2973
                                      · linarith only [h2, h2973, hlam]
                                      · linarith only [h2866, h2973, hlam]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2866, hlam, p2949_0]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2, h2866, h2934, h2943, hc12, hc34, hlam, hphi, ht23, p2949_1]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2, h2866, h2934, h2943, hc13, hc34, hlam, hphi, p2949_1]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [h2942, hlam, p2949_0]
                                    · have p2949_0 := h2949c.1
                                      have p2949_1 := h2949c.2.1
                                      have p2949_2 := h2949c.2.2.1
                                      have p2949_3 := h2949c.2.2.2
                                      linarith only [hlam, p2949_0]
                                  · linarith only [h2, h2866, h2934, h2942, h2943, h2948, hlam]
                                · linarith only [h2, h2866, h2934, h2942, h2947, hlam]
                          · linarith only [h2, h2866, h2942, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
              · linarith only [h2, h2866, h2931, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2985 | h2985
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2986 | h2986
        · linarith only [h0, h2, h2986, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2988 | h2988
          · linarith only [h0, h2866, h2988, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2990 | h2990
            · linarith only [h1, h2866, h2990, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2992 | h2992
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2993 | h2993
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2994 | h2994
                  · linarith only [h0, h2, h2986, h2994, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2996 | h2996
                    · linarith only [h0, h2866, h2988, h2996, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2998 | h2998
                      · linarith only [h1, h2, h2994, h2998, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h2, h2993, h2998, hc23, hc34, hlam, hphi]
                · linarith only [h2985, h2986, h2993, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3002 | h3002
                · linarith only [h0, h2, h2992, h3002, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h2, h2985, h2992, h3002, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3005 | h3005
        · linarith only [h1, h2, h2985, h3005, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3007 | h3007
          · linarith only [h1, h2866, h2985, h3007, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3009 | h3009
            · linarith only [h1, h2866, h3009, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3011 | h3011
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3012 | h3012
                · linarith only [h0, h2866, h2985, h3012, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3014 | h3014
                  · linarith only [h0, h2866, h3005, h3011, h3014, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3016 | h3016
                    · linarith only [h1, h2, h3007, h3012, h3014, h3016, hc02, hc24, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3018 | h3018
                      · linarith only [h1, h2, h3014, h3018, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3020 | h3020
                        · linarith only [h1, h2, h3009, h3018, h3020, hc03, hc34, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3022 | h3022
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3023 | h3023
                            · linarith only [h0, h2866, h3018, h3022, h3023, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3025 | h3025
                              · linarith only [h1, h2866, h3012, h3020, h3023, h3025, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3027 | h3027
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3028 | h3028
                                  · rcases h1bigk with h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h2866, h3016, hc12, hc25, hlam, hphi, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h2866, h3012, h3016, hc12, hc25, hlam, hphi, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h2, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h2866, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h0, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3012, hlam, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3014, hlam, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3016, hlam, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h1, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h1, h2866, h3016, hc12, hc25, hlam, hphi, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3018, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3020, hlam, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h1, h3014, h3023, hc13, hc34, hlam, hphi, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      rcases p3029_3 (m.d 0 1) (by simp) with h3046 | h3046
                                      · linarith only [h2, h3046, hlam]
                                      · linarith only [h0, h3046, hlam]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      rcases p3029_3 (m.d 0 1) (by simp) with h3049 | h3049
                                      · linarith only [h2, h3049, hlam]
                                      · linarith only [h1, h3049, hlam]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h1, h2866, h3012, h3014, h3023, hc12, hc34, hlam, hphi, ht23, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h1, h3012, h3016, h3025, h3028, hc12, hc34, hlam, hphi, ht23, p3029_1]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      rcases p3029_3 (m.d 0 1) (by simp) with h3055 | h3055
                                      · linarith only [h2866, h3055, hlam]
                                      · linarith only [h0, h3055, hlam]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      rcases p3029_3 (m.d 0 1) (by simp) with h3058 | h3058
                                      · linarith only [h2866, h3058, hlam]
                                      · linarith only [h1, h3058, hlam]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [h3022, hlam, p3029_0]
                                    · have p3029_0 := h3029c.1
                                      have p3029_1 := h3029c.2.1
                                      have p3029_2 := h3029c.2.2.1
                                      have p3029_3 := h3029c.2.2.2
                                      linarith only [hlam, p3029_0]
                                  · linarith only [h1, h2, h3011, h3012, h3014, h3023, h3028, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · linarith only [h2, h3011, h3014, h3027, hlam]
                          · linarith only [h2, h3011, h3022, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3066 | h3066
                · linarith only [h0, h2985, h3066, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3068 | h3068
                  · linarith only [h1, h2866, h3066, h3068, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3070 | h3070
                    · linarith only [h1, h2, h3011, h3066, h3070, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3072 | h3072
                      · linarith only [h1, h2, h3011, h3072, hc45, hlam, hphi, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3074 | h3074
                        · linarith only [h1, h2, h3011, h3074, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3076 | h3076
                          · linarith only [h1, h2, h3011, h3066, h3068, h3076, hc12, hc24, hlam, hphi]
                          · linarith only [h1, h2, h3066, h3076, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
