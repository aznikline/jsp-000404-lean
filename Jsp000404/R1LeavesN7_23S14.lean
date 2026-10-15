import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S12
import Jsp000404.R1LeavesN7_23S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1290 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h1381 | h1381
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0_x1_x1_x0 m hb2 hb4 hg0 hg1 h2 h3 h4 h1290 h1381
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0_x1_x1_x1 m hb2 hb4 hg0 hg1 h2 h3 h4 h1290 h1381

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 4 (by decide) (by decide) with h1290 | h1290
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0_x1_x0 m hb2 hb4 hg0 hg1 h2 h3 h4 h1290
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0_x1_x1 m hb2 hb4 hg0 hg1 h2 h3 h4 h1290

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0_x0 m hb2 hb4 hg0 hg1 h2 h3 h4
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0_x1 m hb2 hb4 hg0 hg1 h2 h3 h4

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 3 (by decide) (by decide) with h2261 | h2261
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2262 | h2262
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2263 | h2263
      · linarith only [h0, h2263, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2265 | h2265
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2266 | h2266
          · linarith only [h1, h2265, h2266, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2268 | h2268
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2269 | h2269
              · linarith only [h0, h2269, h3, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h2262, h2263, h2269, hc12, hc25, hlam, hphi]
            · linarith only [h2261, h2263, h2268, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2273 | h2273
          · linarith only [h0, h2262, h2273, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2275 | h2275
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2276 | h2276
              · linarith only [h0, h2276, h3, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h2262, h2263, h2275, h2276, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h2261, h2263, h2275, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2280 | h2280
      · linarith only [h2, h2262, h2280, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2282 | h2282
        · linarith only [h2261, h2262, h2282, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2284 | h2284
          · linarith only [h2, h2284, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2286 | h2286
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2287 | h2287
              · linarith only [h0, h2262, h2287, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2289 | h2289
                · linarith only [h0, h2, h2262, h2280, h2289, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2291 | h2291
                  · linarith only [h1, h2261, h2262, h2284, h2291, hc45, hlam, hphi, u4ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2293 | h2293
                    · linarith only [h2, h2262, h2284, h2289, h2293, h3, hc02, hc25, hlam, hphi]
                    · linarith only [h2, h2286, h2287, h2293, h3, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h2261, h2262, h2286, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2297 | h2297
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2298 | h2298
      · linarith only [h1, h2261, h2298, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2300 | h2300
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2301 | h2301
          · linarith only [h1, h2261, h2297, h2301, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2303 | h2303
            · linarith only [h0, h2261, h2297, h2303, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2305 | h2305
              · linarith only [h1, h2303, h2305, h3, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h2261, h2297, h2305, hc12, hc23, hlam, hphi]
        · linarith only [h2261, h2297, h2300, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2309 | h2309
      · linarith only [h0, h2309, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2311 | h2311
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2312 | h2312
          · linarith only [h1, h2311, h2312, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2314 | h2314
            · linarith only [h0, h2261, h2314, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2316 | h2316
              · linarith only [h0, h2297, h2316, h3, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2318 | h2318
                · linarith only [h0, h2309, h2318, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2320 | h2320
                  · linarith only [h1, h2318, h2320, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h1, h2311, h2314, h2318, h2320, h3, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2323 | h2323
          · linarith only [h2, h2323, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2325 | h2325
            · linarith only [h0, h2261, h2325, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2327 | h2327
              · linarith only [h0, h2297, h2327, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2329 | h2329
                · linarith only [h0, h2309, h2329, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2331 | h2331
                  · linarith only [h1, h2261, h2311, h2329, h2331, h3, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2333 | h2333
                    · linarith only [h2, h2323, h2329, h2333, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · linarith only [h2, h2333, h3, hc45, hlam, hphi, u4ehi1]

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x0 m hb2 hb4 hg0 hg1 h2 h3
  · exact r1l7_12_24_L_I_M_IR_s1_x0_x1 m hb2 hb4 hg0 hg1 h2 h3

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 5 (by decide) (by decide) with h2336 | h2336
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2337 | h2337
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2338 | h2338
      · linarith only [h0, h2, h2338, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2340 | h2340
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2341 | h2341
          · linarith only [h0, h2, h2337, h2341, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2343 | h2343
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2344 | h2344
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2345 | h2345
                · linarith only [h0, h2, h2338, h2345, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2347 | h2347
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2348 | h2348
                    · linarith only [h1, h2, h2341, h2348, hlam]
                    · linarith only [h0, h2, h2344, h2348, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h2, h2340, h2344, h2345, h2347, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h2337, h2338, h2344, hc12, hc24, hlam, hphi]
            · linarith only [h0, h2, h2340, h2343, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2354 | h2354
          · linarith only [h2, h2336, h2337, h2340, h2354, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2356 | h2356
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2357 | h2357
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2358 | h2358
                · linarith only [h0, h2, h2338, h2358, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2360 | h2360
                  · linarith only [h0, h2340, h2360, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2362 | h2362
                    · linarith only [h0, h2, h2354, h2357, h2362, hlam]
                    · linarith only [h2, h2336, h2357, h2360, h2362, hc23, hc34, hlam, hphi]
              · linarith only [h2337, h2340, h2357, hc12, hc25, hlam, hphi]
            · linarith only [h2, h2336, h2356, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2367 | h2367
      · linarith only [h0, h2, h2367, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2369 | h2369
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2370 | h2370
          · linarith only [h1, h2, h2370, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2372 | h2372
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2373 | h2373
              · linarith only [h0, h2, h2337, h2373, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2375 | h2375
                · linarith only [h0, h2, h2367, h2375, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2377 | h2377
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2378 | h2378
                    · linarith only [h1, h2, h2337, h2370, h2378, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2380 | h2380
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2381 | h2381
                        · linarith only [h0, h2, h2377, h2378, h2380, h2381, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2383 | h2383
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2384 | h2384
                            · linarith only [h2337, h2369, h2381, h2384, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · linarith only [h1, h2, h2373, h2377, h2380, h2384, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h1, h2, h2337, h2373, h2375, h2377, h2381, h2383, hc02, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h2, h2373, h2380, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h2337, h2369, h2377, hc12, hc23, hlam, hphi]
            · linarith only [h2, h2336, h2372, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2391 | h2391
          · linarith only [h1, h2, h2391, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2393 | h2393
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2394 | h2394
              · linarith only [h0, h2, h2337, h2394, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2396 | h2396
                · linarith only [h0, h2, h2367, h2396, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2398 | h2398
                  · linarith only [h1, h2, h2369, h2394, h2396, h2398, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2400 | h2400
                    · linarith only [h1, h2, h2391, h2396, h2400, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2402 | h2402
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2403 | h2403
                        · linarith only [h2, h2336, h2400, h2402, h2403, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2405 | h2405
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2406 | h2406
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2407 | h2407
                              · rcases h2bigk with h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c | h2408c
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2369, hc12, hc25, hlam, hphi, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2337, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2367, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2369, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h0, hlam, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2394, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2396, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2398, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2403, hc02, hc34, hlam, hphi, ht23, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2403, hc12, hc34, hlam, hphi, ht23, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2403, hlam, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h0, h2369, h2403, hc12, hc34, hlam, hphi, ht23, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  rcases p2408_3 (m.d 0 2) (by simp) with h2424 | h2424
                                  · linarith only [h2424, hlam, p2408_0]
                                  · rcases p2408_3 (m.d 1 2) (by simp) with h2426 | h2426
                                    · linarith only [h2396, h2426, hlam]
                                    · rcases p2408_3 (m.d 2 3) (by simp) with h2428 | h2428
                                      · linarith only [h2403, h2428, hlam]
                                      · linarith only [h2337, h2428, hlam]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  rcases p2408_3 (m.d 0 2) (by simp) with h2431 | h2431
                                  · linarith only [h2367, h2431, hlam]
                                  · linarith only [h0, h2431, hlam]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h0, h2337, hc12, hc24, hlam, hphi, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h0, h2369, h2403, hc12, hc34, hlam, hphi, ht23, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h0, h2403, h2405, hc12, hc34, hlam, hphi, ht23, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2403, h2405, hc12, hc34, hlam, hphi, ht23, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2405, hlam, p2408_0]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [h2406, hlam, p2408_1]
                                · have p2408_0 := h2408c.1
                                  have p2408_1 := h2408c.2.1
                                  have p2408_2 := h2408c.2.2.1
                                  have p2408_3 := h2408c.2.2.2
                                  linarith only [hlam, p2408_0]
                              · linarith only [h2, h2336, h2402, h2403, h2407, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h2, h2336, h2396, h2402, h2406, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2444 | h2444
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2445 | h2445
                              · rcases h2bigk with h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c | h2446c
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h0, h2, h2396, h2403, hc12, hc34, hlam, hphi, ht23, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2337, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2367, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2369, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h0, hlam, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2394, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2396, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2398, hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2405, hc02, hc35, hlam, hphi, ht23, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2405, hc12, hc35, hlam, hphi, ht23, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2403, hlam, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2405, hlam, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  rcases p2446_3 (m.d 0 2) (by simp) with h2462 | h2462
                                  · linarith only [h2462, hlam, p2446_0]
                                  · rcases p2446_3 (m.d 1 2) (by simp) with h2464 | h2464
                                    · linarith only [h2396, h2464, hlam]
                                    · rcases p2446_3 (m.d 2 3) (by simp) with h2466 | h2466
                                      · linarith only [h2403, h2466, hlam]
                                      · linarith only [h2337, h2466, hlam]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  rcases p2446_3 (m.d 0 2) (by simp) with h2469 | h2469
                                  · linarith only [h2367, h2469, hlam]
                                  · linarith only [h0, h2469, hlam]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h0, h2337, h2403, hc12, hc34, hlam, hphi, ht23, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [hlam, p2446_0]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h0, h2337, h2403, h2405, hc12, hc34, hlam, hphi, ht23, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  rcases p2446_3 (m.d 0 2) (by simp) with h2475 | h2475
                                  · linarith only [h2475, hlam, p2446_0]
                                  · rcases p2446_3 (m.d 1 2) (by simp) with h2477 | h2477
                                    · linarith only [h2398, h2477, hlam]
                                    · rcases p2446_3 (m.d 2 3) (by simp) with h2479 | h2479
                                      · linarith only [h2405, h2479, hlam]
                                      · linarith only [h2337, h2479, hlam]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  rcases p2446_3 (m.d 0 2) (by simp) with h2482 | h2482
                                  · linarith only [h2369, h2482, hlam]
                                  · linarith only [h0, h2482, hlam]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h0, h2337, hc12, hc25, hlam, hphi, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [h2444, hlam, p2446_1]
                                · have p2446_0 := h2446c.1
                                  have p2446_1 := h2446c.2.1
                                  have p2446_2 := h2446c.2.2.1
                                  have p2446_3 := h2446c.2.2.2
                                  linarith only [hlam, p2446_0]
                              · linarith only [h2, h2336, h2396, h2402, h2403, h2445, hlam]
                            · linarith only [h2, h2336, h2396, h2402, h2444, hlam]
                      · linarith only [h0, h2, h2402, hc12, hc45, hlam, hphi, ht23, ht34]
            · linarith only [h2, h2336, h2393, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2492 | h2492
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2493 | h2493
      · linarith only [h0, h2, h2493, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2495 | h2495
        · linarith only [h0, h2336, h2495, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2497 | h2497
          · linarith only [h0, h2, h2492, h2497, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2499 | h2499
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2500 | h2500
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2501 | h2501
                · linarith only [h0, h2, h2493, h2501, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2503 | h2503
                  · linarith only [h0, h2336, h2495, h2503, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2505 | h2505
                    · linarith only [h0, h1, h2336, h2492, h2497, h2499, h2505, hlam]
                    · linarith only [h0, h2, h2500, h2505, hc23, hc34, hlam, hphi]
              · linarith only [h2492, h2493, h2500, hc12, hc24, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2509 | h2509
              · linarith only [h0, h2, h2499, h2509, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h2, h2492, h2499, h2509, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2512 | h2512
      · linarith only [h1, h2, h2492, h2512, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2514 | h2514
        · linarith only [h1, h2336, h2492, h2514, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2516 | h2516
          · linarith only [h1, h2, h2516, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2518 | h2518
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2519 | h2519
              · linarith only [h0, h2, h2492, h2519, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2521 | h2521
                · linarith only [h0, h2336, h2512, h2518, h2521, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2523 | h2523
                  · linarith only [h1, h2, h2514, h2519, h2521, h2523, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2525 | h2525
                    · linarith only [h1, h2, h2516, h2521, h2525, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2527 | h2527
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2528 | h2528
                        · linarith only [h0, h2336, h2525, h2527, h2528, hc12, hc23, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2530 | h2530
                          · linarith only [h1, h2336, h2519, h2523, h2528, h2530, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2532 | h2532
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2533 | h2533
                              · rcases h2bigk with h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c | h2534c
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [hlam, p2534_0]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h0, h2336, h2521, h2527, hc12, hc24, hlam, hphi, p2534_1]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h2492, hlam, p2534_0]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h2512, hlam, p2534_0]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h2514, hlam, p2534_0]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h0, hlam, p2534_1]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [hlam, p2534_0]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h2519, hlam, p2534_0]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h2521, hlam, p2534_0]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h2523, hlam, p2534_0]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h2530, h2533, hc02, hc34, hlam, hphi, ht23, p2534_1]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h2530, h2533, hc12, hc34, hlam, hphi, ht23, p2534_1]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [hlam, p2534_0]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h2528, hlam, p2534_1]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h2530, hlam, p2534_1]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  rcases p2534_3 (m.d 0 2) (by simp) with h2550 | h2550
                                  · linarith only [h2550, hlam, p2534_0]
                                  · rcases p2534_3 (m.d 1 2) (by simp) with h2552 | h2552
                                    · linarith only [h2521, h2552, hlam]
                                    · rcases p2534_3 (m.d 2 3) (by simp) with h2554 | h2554
                                      · linarith only [h2528, h2554, hlam]
                                      · linarith only [h2492, h2554, hlam]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  rcases p2534_3 (m.d 0 2) (by simp) with h2557 | h2557
                                  · linarith only [h2512, h2557, hlam]
                                  · linarith only [h0, h2557, hlam]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h0, h2492, h2528, hc12, hc34, hlam, hphi, ht23, p2534_1]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [hlam, p2534_0]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h2336, h2523, h2528, hc01, hc34, hlam, hphi, ht12, ht23, p2534_1]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  rcases p2534_3 (m.d 0 2) (by simp) with h2563 | h2563
                                  · linarith only [h2563, hlam, p2534_0]
                                  · rcases p2534_3 (m.d 1 2) (by simp) with h2565 | h2565
                                    · linarith only [h2523, h2565, hlam]
                                    · rcases p2534_3 (m.d 2 3) (by simp) with h2567 | h2567
                                      · linarith only [h2530, h2567, hlam]
                                      · linarith only [h2492, h2567, hlam]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  rcases p2534_3 (m.d 0 2) (by simp) with h2570 | h2570
                                  · linarith only [h2514, h2570, hlam]
                                  · linarith only [h0, h2570, hlam]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h0, h2492, hc12, hc25, hlam, hphi, p2534_1]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [h2532, hlam, p2534_1]
                                · have p2534_0 := h2534c.1
                                  have p2534_1 := h2534c.2.1
                                  have p2534_2 := h2534c.2.2.1
                                  have p2534_3 := h2534c.2.2.2
                                  linarith only [hlam, p2534_0]
                              · linarith only [h1, h2, h2518, h2519, h2521, h2528, h2533, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h2, h2518, h2521, h2532, hlam]
                      · linarith only [h2, h2518, h2527, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2579 | h2579
              · linarith only [h0, h2492, h2579, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2581 | h2581
                · linarith only [h0, h2336, h2581, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2583 | h2583
                  · linarith only [h0, h2514, h2583, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2585 | h2585
                    · linarith only [h1, h2, h2516, h2585, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2587 | h2587
                      · linarith only [h1, h2, h2518, h2579, h2581, h2587, hc12, hc24, hlam, hphi]
                      · linarith only [h1, h2, h2579, h2587, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5176000 in
set_option maxHeartbeats 5176000 in
theorem r1l7_12_24_L_I_M_IR_s1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_12_24_L_I_M_IR_s1_x0 m hb2 hb4 hg0 hg1 h2
  · exact r1l7_12_24_L_I_M_IR_s1_x1 m hb2 hb4 hg0 hg1 h2

end R2N4
