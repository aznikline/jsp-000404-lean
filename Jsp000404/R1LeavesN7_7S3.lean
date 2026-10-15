import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2202 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 4 (by decide) (by decide) with h2203 | h2203
  · rcases m.htr 1 2 5 (by decide) (by decide) with h2204 | h2204
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2205 | h2205
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2206 | h2206
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2207 | h2207
          · linarith only [h2, h2207, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2209 | h2209
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2210 | h2210
              · linarith only [h0, h2202, h2210, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h0, h2202, h2206, h2209, h2210, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2213 | h2213
              · linarith only [h2, h2205, h2209, h2213, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2215 | h2215
                · linarith only [h0, h2202, h2205, h2209, h2215, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2217 | h2217
                  · linarith only [h2, h2205, h2217, h9, hlam]
                  · rcases h1bigk with h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c | h2219c
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [hlam, p2219_0]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h2202, h2206, h2209, h2217, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2219_1]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h2206, h2209, h2217, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2219_1]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      rcases p2219_3 (m.d 0 1) (by simp) with h2223 | h2223
                      · rcases p2219_3 (m.d 1 2) (by simp) with h2224 | h2224
                        · linarith only [h0, h2224, hlam]
                        · linarith only [h2203, h2224, hlam]
                      · linarith only [h2223, hlam, p2219_0]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      rcases p2219_3 (m.d 0 1) (by simp) with h2228 | h2228
                      · rcases p2219_3 (m.d 1 2) (by simp) with h2229 | h2229
                        · linarith only [h0, h2229, hlam]
                        · linarith only [h2204, h2229, hlam]
                      · linarith only [h2228, hlam, p2219_0]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h0, hlam, p2219_0]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [hlam, p2219_0]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h2206, h2209, h2217, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2219_1]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h0, h2205, h2209, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2219_1]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h0, h2206, h2209, h2217, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2219_1]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h1, hlam, p2219_0]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h2202, hlam, p2219_1]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [hlam, p2219_0]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h1, h2205, h2209, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2219_1]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h0, h2202, h2206, h2209, h2217, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2219_1]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h2, hlam, p2219_0]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h2203, hlam, p2219_1]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h2205, hlam, p2219_0]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [hlam, p2219_0]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h2207, hlam, p2219_1]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h3, hlam, p2219_0]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h2204, hlam, p2219_1]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h2206, hlam, p2219_0]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [h2205, h2209, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2219_1]
                    · have p2219_0 := h2219c.1
                      have p2219_1 := h2219c.2.1
                      have p2219_2 := h2219c.2.2.1
                      have p2219_3 := h2219c.2.2.2
                      linarith only [hlam, p2219_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2253 | h2253
          · linarith only [h2, h2205, h2206, h2253, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2255 | h2255
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2256 | h2256
              · linarith only [h2202, h2206, h2256, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2258 | h2258
                · linarith only [h2203, h2205, h2206, h2258, h4, h8, h9, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2260 | h2260
                  · linarith only [h2202, h2206, h2255, h2260, h8, h9, hlam]
                  · rcases h1bigk with h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c | h2262c
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [hlam, p2262_0]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h2204, hc01, hlam, hphi, ht0b, ht5b, p2262_1, u5ehi2]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      rcases p2262_3 (m.d 0 1) (by simp) with h2265 | h2265
                      · rcases p2262_3 (m.d 1 2) (by simp) with h2266 | h2266
                        · linarith only [h0, h2266, hlam]
                        · linarith only [h2202, h2266, hlam]
                      · linarith only [h2265, hlam, p2262_0]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      rcases p2262_3 (m.d 0 1) (by simp) with h2270 | h2270
                      · rcases p2262_3 (m.d 1 2) (by simp) with h2271 | h2271
                        · linarith only [h0, h2271, hlam]
                        · linarith only [h2203, h2271, hlam]
                      · linarith only [h2270, hlam, p2262_0]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      rcases p2262_3 (m.d 0 1) (by simp) with h2275 | h2275
                      · rcases p2262_3 (m.d 1 2) (by simp) with h2276 | h2276
                        · linarith only [h0, h2276, hlam]
                        · linarith only [h2204, h2276, hlam]
                      · linarith only [h2275, hlam, p2262_0]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h0, hlam, p2262_0]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [hlam, p2262_0]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h0, h2202, h2255, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2262_1]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      rcases p2262_3 (m.d 0 1) (by simp) with h2283 | h2283
                      · rcases p2262_3 (m.d 1 2) (by simp) with h2284 | h2284
                        · rcases p2262_3 (m.d 1 3) (by simp) with h2285 | h2285
                          · linarith only [h2202, h2285, hlam]
                          · linarith only [h2205, h2285, hlam]
                        · linarith only [h2203, h2284, hlam]
                      · linarith only [h2, h2283, hlam]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p2262_1, u5ehi1]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h1, hlam, p2262_0]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h2202, hlam, p2262_1]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [hlam, p2262_0]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h2206, h4, h8, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p2262_1]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h2206, hlam, p2262_1]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h2, hlam, p2262_0]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h2203, hlam, p2262_1]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h2205, hlam, p2262_0]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [hlam, p2262_0]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h2253, hlam, p2262_1]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h3, hlam, p2262_0]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h2204, hlam, p2262_1]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [h0, h2204, h2205, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2262_1]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      rcases p2262_3 (m.d 0 1) (by simp) with h2304 | h2304
                      · rcases p2262_3 (m.d 1 2) (by simp) with h2305 | h2305
                        · rcases p2262_3 (m.d 1 3) (by simp) with h2306 | h2306
                          · linarith only [h2206, h2306, hlam]
                          · linarith only [h2205, h2306, hlam]
                        · linarith only [h2203, h2305, hlam]
                      · linarith only [h2, h2304, hlam]
                    · have p2262_0 := h2262c.1
                      have p2262_1 := h2262c.2.1
                      have p2262_2 := h2262c.2.2.1
                      have p2262_3 := h2262c.2.2.2
                      linarith only [hlam, p2262_0]
            · linarith only [h0, h2205, h2206, h2255, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2313 | h2313
        · linarith only [h2205, h2313, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2315 | h2315
          · linarith only [h2205, h2315, h7, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2317 | h2317
            · linarith only [h2202, h2205, h2317, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2319 | h2319
              · linarith only [h2202, h2205, h2313, h2319, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2321 | h2321
                · linarith only [h2, h2203, h2321, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2323 | h2323
                  · linarith only [h2323, h7, h9, hlam]
                  · rcases h1bigk with h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c | h2325c
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2204, hc01, hlam, hphi, ht0b, ht5b, p2325_1, u5ehi2]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 1) (by simp) with h2328 | h2328
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2329 | h2329
                        · linarith only [h0, h2329, hlam]
                        · linarith only [h2202, h2329, hlam]
                      · linarith only [h2328, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 1) (by simp) with h2333 | h2333
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2334 | h2334
                        · linarith only [h0, h2334, hlam]
                        · linarith only [h2203, h2334, hlam]
                      · linarith only [h2333, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 1) (by simp) with h2338 | h2338
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2339 | h2339
                        · linarith only [h0, h2339, hlam]
                        · linarith only [h2204, h2339, hlam]
                      · linarith only [h2338, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h0, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 1) (by simp) with h2345 | h2345
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2346 | h2346
                        · rcases p2325_3 (m.d 1 3) (by simp) with h2347 | h2347
                          · linarith only [h2202, h2347, hlam]
                          · rcases p2325_3 (m.d 1 4) (by simp) with h2349 | h2349
                            · linarith only [h2203, h2349, hlam]
                            · linarith only [h2205, h2349, hlam]
                        · linarith only [h2202, h2346, hlam]
                      · linarith only [h1, h2345, hlam]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 1) (by simp) with h2354 | h2354
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2355 | h2355
                        · rcases p2325_3 (m.d 1 3) (by simp) with h2356 | h2356
                          · linarith only [h2202, h2356, hlam]
                          · rcases p2325_3 (m.d 1 4) (by simp) with h2358 | h2358
                            · linarith only [h2203, h2358, hlam]
                            · rcases p2325_3 (m.d 1 5) (by simp) with h2360 | h2360
                              · linarith only [h2204, h2360, hlam]
                              · linarith only [h2315, h2360, hlam]
                        · linarith only [h2203, h2355, hlam]
                      · linarith only [h2, h2354, hlam]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p2325_1, u5ehi1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h1, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2202, hlam, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2205, hlam, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2313, hlam, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2203, hlam, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2, h2202, h9, hc23, hc45, hlam, hphi, ht34, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2315, hlam, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h3, hlam, p2325_0]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [h2204, hlam, p2325_1]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 1) (by simp) with h2378 | h2378
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2379 | h2379
                        · rcases p2325_3 (m.d 1 3) (by simp) with h2380 | h2380
                          · linarith only [h2313, h2380, hlam]
                          · rcases p2325_3 (m.d 1 4) (by simp) with h2382 | h2382
                            · linarith only [h2315, h2382, hlam]
                            · linarith only [h2205, h2382, hlam]
                        · linarith only [h2202, h2379, hlam]
                      · linarith only [h1, h2378, hlam]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      rcases p2325_3 (m.d 0 1) (by simp) with h2387 | h2387
                      · rcases p2325_3 (m.d 1 2) (by simp) with h2388 | h2388
                        · rcases p2325_3 (m.d 1 3) (by simp) with h2389 | h2389
                          · linarith only [h2313, h2389, hlam]
                          · rcases p2325_3 (m.d 1 4) (by simp) with h2391 | h2391
                            · linarith only [h2315, h2391, hlam]
                            · rcases p2325_3 (m.d 1 5) (by simp) with h2393 | h2393
                              · rcases h1emax with h2394 | h2394 | h2394 | h2394 | h2394
                                · linarith only [h0, h2394, h4, h8, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · linarith only [h2202, h2204, h2205, h2394, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2325_1]
                                · rcases h3bigk with h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c | h2397c
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2205, h2313, h8, hlam, p2325_1, p2397_2]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2202, h2205, h2313, h8, hlam, p2325_1, p2397_2]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    rcases p2397_3 (m.d 0 3) (by simp) with h2401 | h2401
                                    · rcases p2397_3 (m.d 1 3) (by simp) with h2402 | h2402
                                      · linarith only [h1, h2402, hlam]
                                      · rcases p2397_3 (m.d 2 3) (by simp) with h2404 | h2404
                                        · linarith only [h2404, h4, hlam]
                                        · rcases p2397_3 (m.d 3 4) (by simp) with h2406 | h2406
                                          · linarith only [h2406, hlam, p2397_0]
                                          · rcases p2397_3 (m.d 3 5) (by simp) with h2408 | h2408
                                            · linarith only [h2408, h8, hlam]
                                            · linarith only [h2323, h2408, hlam]
                                    · linarith only [h2401, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h0, h2202, h2205, h2313, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2325_1, p2397_1]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h1, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2205, h2313, h8, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2325_1, p2397_1]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2205, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2313, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h4, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2202, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2317, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2319, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h7, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2202, h7, h9, hc23, hc45, hlam, hphi, ht34, p2397_1]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h7, h9, hc23, hc45, hlam, hphi, ht34, p2397_1]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h2323, hlam, p2397_1]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h8, hlam, p2397_0]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    rcases p2397_3 (m.d 0 3) (by simp) with h2429 | h2429
                                    · rcases p2397_3 (m.d 1 3) (by simp) with h2430 | h2430
                                      · linarith only [h2430, hlam, p2397_0]
                                      · rcases p2397_3 (m.d 2 3) (by simp) with h2432 | h2432
                                        · linarith only [h2319, h2432, hlam]
                                        · rcases p2397_3 (m.d 3 4) (by simp) with h2434 | h2434
                                          · linarith only [h2323, h2434, hlam]
                                          · linarith only [h2205, h2434, hlam]
                                    · linarith only [h1, h2429, hlam]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    rcases p2397_3 (m.d 0 3) (by simp) with h2438 | h2438
                                    · rcases p2397_3 (m.d 1 3) (by simp) with h2439 | h2439
                                      · linarith only [h2313, h2439, hlam]
                                      · linarith only [h2202, h2439, hlam]
                                    · linarith only [h2438, h4, hlam]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [h0, h2202, h2205, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2397_1]
                                  · have p2397_0 := h2397c.1
                                    have p2397_1 := h2397c.2.1
                                    have p2397_2 := h2397c.2.2.1
                                    have p2397_3 := h2397c.2.2.2
                                    linarith only [hlam, p2397_0]
                                · rcases h3bigk with h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2205, h2313, h8, hlam, p2325_1, p2445_2]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2202, h2205, h2313, h8, hlam, p2325_1, p2445_2]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    rcases p2445_3 (m.d 0 3) (by simp) with h2449 | h2449
                                    · rcases p2445_3 (m.d 1 3) (by simp) with h2450 | h2450
                                      · linarith only [h1, h2450, hlam]
                                      · rcases p2445_3 (m.d 2 3) (by simp) with h2452 | h2452
                                        · linarith only [h2452, h4, hlam]
                                        · rcases p2445_3 (m.d 3 4) (by simp) with h2454 | h2454
                                          · linarith only [h2454, hlam, p2445_0]
                                          · rcases p2445_3 (m.d 3 5) (by simp) with h2456 | h2456
                                            · linarith only [h2456, h8, hlam]
                                            · linarith only [h2323, h2456, hlam]
                                    · linarith only [h2449, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h0, h2205, h2313, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2325_1, p2445_1]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h1, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2205, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2325_1, p2445_1]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2205, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2313, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h4, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2202, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2317, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2319, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h7, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2202, h7, h9, hc23, hc45, hlam, hphi, ht34, p2445_1]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h7, h9, hc23, hc45, hlam, hphi, ht34, p2445_1]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2323, hlam, p2445_1]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h8, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    rcases p2445_3 (m.d 0 3) (by simp) with h2477 | h2477
                                    · rcases p2445_3 (m.d 1 3) (by simp) with h2478 | h2478
                                      · linarith only [h2478, hlam, p2445_0]
                                      · rcases p2445_3 (m.d 2 3) (by simp) with h2480 | h2480
                                        · linarith only [h2319, h2480, hlam]
                                        · rcases p2445_3 (m.d 3 4) (by simp) with h2482 | h2482
                                          · linarith only [h2323, h2482, hlam]
                                          · linarith only [h2205, h2482, hlam]
                                    · linarith only [h1, h2477, hlam]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    rcases p2445_3 (m.d 0 3) (by simp) with h2486 | h2486
                                    · rcases p2445_3 (m.d 1 3) (by simp) with h2487 | h2487
                                      · linarith only [h2313, h2487, hlam]
                                      · linarith only [h2202, h2487, hlam]
                                    · linarith only [h2486, h4, hlam]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h0, h2202, h2205, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2445_1]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [hlam, p2445_0]
                                · linarith only [h2394, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2325_1]
                              · linarith only [h2315, h2393, hlam]
                        · linarith only [h2203, h2388, hlam]
                      · linarith only [h2, h2387, hlam]
                    · have p2325_0 := h2325c.1
                      have p2325_1 := h2325c.2.1
                      have p2325_2 := h2325c.2.2.1
                      have p2325_3 := h2325c.2.2.2
                      linarith only [hlam, p2325_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2498 | h2498
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2499 | h2499
        · linarith only [h0, h2202, h2204, h2499, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2501 | h2501
          · linarith only [h2, h2501, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2503 | h2503
            · linarith only [h0, h2202, h2204, h2503, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h2202, h2204, h2498, h2503, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2506 | h2506
        · linarith only [h0, h2498, h2506, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2508 | h2508
          · linarith only [h0, h2203, h2204, h2508, h6, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2510 | h2510
            · linarith only [h2202, h2498, h2510, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2512 | h2512
              · linarith only [h2202, h2498, h2506, h2512, h7, hc03, hlam, hphi, ht0b, ht5b, u5ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2514 | h2514
                · linarith only [h2203, h2498, h2514, h7, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2516 | h2516
                  · linarith only [h2203, h2204, h2512, h2516, h7, h8, h9, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h1bigk with h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c | h2518c
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      rcases p2518_3 (m.d 0 1) (by simp) with h2520 | h2520
                      · rcases p2518_3 (m.d 1 2) (by simp) with h2521 | h2521
                        · linarith only [h2521, hlam, p2518_0]
                        · rcases p2518_3 (m.d 1 3) (by simp) with h2523 | h2523
                          · linarith only [h1, h2523, hlam]
                          · rcases p2518_3 (m.d 1 4) (by simp) with h2525 | h2525
                            · linarith only [h2, h2525, hlam]
                            · rcases p2518_3 (m.d 1 5) (by simp) with h2527 | h2527
                              · linarith only [h2527, h3, hlam]
                              · linarith only [h2204, h2527, hlam]
                      · linarith only [h2520, hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      rcases p2518_3 (m.d 0 1) (by simp) with h2531 | h2531
                      · rcases p2518_3 (m.d 1 2) (by simp) with h2532 | h2532
                        · linarith only [h0, h2532, hlam]
                        · linarith only [h2202, h2532, hlam]
                      · linarith only [h2531, hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      rcases p2518_3 (m.d 0 1) (by simp) with h2536 | h2536
                      · rcases p2518_3 (m.d 1 2) (by simp) with h2537 | h2537
                        · linarith only [h0, h2537, hlam]
                        · linarith only [h2203, h2537, hlam]
                      · linarith only [h2536, hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      rcases p2518_3 (m.d 0 1) (by simp) with h2541 | h2541
                      · rcases p2518_3 (m.d 1 2) (by simp) with h2542 | h2542
                        · linarith only [h0, h2542, hlam]
                        · rcases p2518_3 (m.d 1 3) (by simp) with h2544 | h2544
                          · linarith only [h1, h2544, hlam]
                          · rcases p2518_3 (m.d 1 4) (by simp) with h2546 | h2546
                            · linarith only [h2, h2546, hlam]
                            · rcases p2518_3 (m.d 1 5) (by simp) with h2548 | h2548
                              · linarith only [h2548, hlam, p2518_0]
                              · rcases h1emax with h2550 | h2550 | h2550 | h2550 | h2550
                                · linarith only [h2550, hlam, hphi, ht01, ht0b, ht5b, p2518_1, u5ehi1]
                                · rcases h3bigk with h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c | h2552c
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    rcases p2552_3 (m.d 0 3) (by simp) with h2554 | h2554
                                    · rcases p2552_3 (m.d 1 3) (by simp) with h2555 | h2555
                                      · linarith only [h1, h2555, hlam]
                                      · rcases p2552_3 (m.d 2 3) (by simp) with h2557 | h2557
                                        · linarith only [h2557, h4, hlam]
                                        · rcases p2552_3 (m.d 3 4) (by simp) with h2559 | h2559
                                          · linarith only [h2559, h7, hlam]
                                          · linarith only [h2498, h2559, hlam]
                                    · linarith only [h1, h2554, hlam]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2203, h2204, h2510, h2512, h8, hlam, p2552_2]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    rcases p2552_3 (m.d 0 3) (by simp) with h2564 | h2564
                                    · rcases p2552_3 (m.d 1 3) (by simp) with h2565 | h2565
                                      · linarith only [h1, h2565, hlam]
                                      · rcases p2552_3 (m.d 2 3) (by simp) with h2567 | h2567
                                        · linarith only [h2567, h4, hlam]
                                        · rcases p2552_3 (m.d 3 4) (by simp) with h2569 | h2569
                                          · linarith only [h2569, hlam, p2552_0]
                                          · rcases p2552_3 (m.d 3 5) (by simp) with h2571 | h2571
                                            · linarith only [h2571, h8, hlam]
                                            · linarith only [h2516, h2571, hlam]
                                    · linarith only [h2564, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h0, h2203, h2204, h2510, h2512, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h1, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2498, hc23, hc34, hlam, hphi, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2498, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2506, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h4, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2202, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2510, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2512, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h7, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h7, h9, hc13, hc45, hlam, hphi, ht34, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h7, h9, hc23, hc45, hlam, hphi, ht34, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2516, hlam, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h8, hlam, p2552_0]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    rcases p2552_3 (m.d 0 3) (by simp) with h2592 | h2592
                                    · rcases p2552_3 (m.d 1 3) (by simp) with h2593 | h2593
                                      · linarith only [h2593, hlam, p2552_0]
                                      · rcases p2552_3 (m.d 2 3) (by simp) with h2595 | h2595
                                        · linarith only [h2512, h2595, hlam]
                                        · rcases p2552_3 (m.d 3 4) (by simp) with h2597 | h2597
                                          · linarith only [h2516, h2597, hlam]
                                          · linarith only [h2498, h2597, hlam]
                                    · linarith only [h1, h2592, hlam]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    rcases p2552_3 (m.d 0 3) (by simp) with h2601 | h2601
                                    · rcases p2552_3 (m.d 1 3) (by simp) with h2602 | h2602
                                      · linarith only [h2506, h2602, hlam]
                                      · linarith only [h2202, h2602, hlam]
                                    · linarith only [h2601, h4, hlam]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [h2202, h2498, hc23, hc35, hlam, hphi, p2552_1]
                                  · have p2552_0 := h2552c.1
                                    have p2552_1 := h2552c.2.1
                                    have p2552_2 := h2552c.2.2.1
                                    have p2552_3 := h2552c.2.2.2
                                    linarith only [hlam, p2552_0]
                                · rcases h3bigk with h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c | h2608c
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    rcases p2608_3 (m.d 0 3) (by simp) with h2610 | h2610
                                    · rcases p2608_3 (m.d 1 3) (by simp) with h2611 | h2611
                                      · linarith only [h1, h2611, hlam]
                                      · rcases p2608_3 (m.d 2 3) (by simp) with h2613 | h2613
                                        · linarith only [h2613, h4, hlam]
                                        · rcases p2608_3 (m.d 3 4) (by simp) with h2615 | h2615
                                          · linarith only [h2615, h7, hlam]
                                          · linarith only [h2498, h2615, hlam]
                                    · linarith only [h1, h2610, hlam]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h2203, h2204, h2510, h2512, h8, hlam, p2608_2]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    rcases p2608_3 (m.d 0 3) (by simp) with h2620 | h2620
                                    · rcases p2608_3 (m.d 1 3) (by simp) with h2621 | h2621
                                      · linarith only [h1, h2621, hlam]
                                      · rcases p2608_3 (m.d 2 3) (by simp) with h2623 | h2623
                                        · linarith only [h2623, h4, hlam]
                                        · rcases p2608_3 (m.d 3 4) (by simp) with h2625 | h2625
                                          · linarith only [h2625, hlam, p2608_0]
                                          · rcases p2608_3 (m.d 3 5) (by simp) with h2627 | h2627
                                            · linarith only [h2627, h8, hlam]
                                            · linarith only [h2516, h2627, hlam]
                                    · linarith only [h2620, hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h2203, h2204, h2510, h2512, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2608_1]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h1, hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h2498, hc23, hc34, hlam, hphi, p2608_1]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h2498, hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h2506, hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h4, hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h2202, hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h2510, hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h2512, hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h7, hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h7, h9, hc13, hc45, hlam, hphi, ht34, p2608_1]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h7, h9, hc23, hc45, hlam, hphi, ht34, p2608_1]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h2516, hlam, p2608_1]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h8, hlam, p2608_0]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    rcases p2608_3 (m.d 0 3) (by simp) with h2648 | h2648
                                    · rcases p2608_3 (m.d 1 3) (by simp) with h2649 | h2649
                                      · linarith only [h2649, hlam, p2608_0]
                                      · rcases p2608_3 (m.d 2 3) (by simp) with h2651 | h2651
                                        · linarith only [h2512, h2651, hlam]
                                        · rcases p2608_3 (m.d 3 4) (by simp) with h2653 | h2653
                                          · linarith only [h2516, h2653, hlam]
                                          · linarith only [h2498, h2653, hlam]
                                    · linarith only [h1, h2648, hlam]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    rcases p2608_3 (m.d 0 3) (by simp) with h2657 | h2657
                                    · rcases p2608_3 (m.d 1 3) (by simp) with h2658 | h2658
                                      · linarith only [h2506, h2658, hlam]
                                      · linarith only [h2202, h2658, hlam]
                                    · linarith only [h2657, h4, hlam]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [h2202, h2498, hc23, hc35, hlam, hphi, p2608_1]
                                  · have p2608_0 := h2608c.1
                                    have p2608_1 := h2608c.2.1
                                    have p2608_2 := h2608c.2.2.1
                                    have p2608_3 := h2608c.2.2.2
                                    linarith only [hlam, p2608_0]
                                · rcases h3bigk with h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c | h2664c
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    rcases p2664_3 (m.d 0 3) (by simp) with h2666 | h2666
                                    · rcases p2664_3 (m.d 1 3) (by simp) with h2667 | h2667
                                      · linarith only [h1, h2667, hlam]
                                      · rcases p2664_3 (m.d 2 3) (by simp) with h2669 | h2669
                                        · linarith only [h2669, h4, hlam]
                                        · rcases p2664_3 (m.d 3 4) (by simp) with h2671 | h2671
                                          · linarith only [h2671, h7, hlam]
                                          · linarith only [h2498, h2671, hlam]
                                    · linarith only [h1, h2666, hlam]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h2203, h2204, h2510, h2512, h8, hlam, p2664_2]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    rcases p2664_3 (m.d 0 3) (by simp) with h2676 | h2676
                                    · rcases p2664_3 (m.d 1 3) (by simp) with h2677 | h2677
                                      · linarith only [h1, h2677, hlam]
                                      · rcases p2664_3 (m.d 2 3) (by simp) with h2679 | h2679
                                        · linarith only [h2679, h4, hlam]
                                        · rcases p2664_3 (m.d 3 4) (by simp) with h2681 | h2681
                                          · linarith only [h2681, hlam, p2664_0]
                                          · rcases p2664_3 (m.d 3 5) (by simp) with h2683 | h2683
                                            · linarith only [h2683, h8, hlam]
                                            · linarith only [h2516, h2683, hlam]
                                    · linarith only [h2676, hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h2203, h2204, h2510, h2512, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2664_1]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h1, hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h2498, hc23, hc34, hlam, hphi, p2664_1]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h2498, hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h2506, hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h4, hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h2202, hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h2510, hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h2512, hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h7, hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h7, h9, hc13, hc45, hlam, hphi, ht34, p2664_1]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h7, h9, hc23, hc45, hlam, hphi, ht34, p2664_1]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h2516, hlam, p2664_1]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h8, hlam, p2664_0]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    rcases p2664_3 (m.d 0 3) (by simp) with h2704 | h2704
                                    · rcases p2664_3 (m.d 1 3) (by simp) with h2705 | h2705
                                      · linarith only [h2705, hlam, p2664_0]
                                      · rcases p2664_3 (m.d 2 3) (by simp) with h2707 | h2707
                                        · linarith only [h2512, h2707, hlam]
                                        · rcases p2664_3 (m.d 3 4) (by simp) with h2709 | h2709
                                          · linarith only [h2516, h2709, hlam]
                                          · linarith only [h2498, h2709, hlam]
                                    · linarith only [h1, h2704, hlam]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    rcases p2664_3 (m.d 0 3) (by simp) with h2713 | h2713
                                    · rcases p2664_3 (m.d 1 3) (by simp) with h2714 | h2714
                                      · linarith only [h2506, h2714, hlam]
                                      · linarith only [h2202, h2714, hlam]
                                    · linarith only [h2713, h4, hlam]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [h2202, h2498, hc23, hc35, hlam, hphi, p2664_1]
                                  · have p2664_0 := h2664c.1
                                    have p2664_1 := h2664c.2.1
                                    have p2664_2 := h2664c.2.2.1
                                    have p2664_3 := h2664c.2.2.2
                                    linarith only [hlam, p2664_0]
                                · rcases h3bigk with h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c | h2720c
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    rcases p2720_3 (m.d 0 3) (by simp) with h2722 | h2722
                                    · rcases p2720_3 (m.d 1 3) (by simp) with h2723 | h2723
                                      · linarith only [h1, h2723, hlam]
                                      · rcases p2720_3 (m.d 2 3) (by simp) with h2725 | h2725
                                        · linarith only [h2725, h4, hlam]
                                        · rcases p2720_3 (m.d 3 4) (by simp) with h2727 | h2727
                                          · linarith only [h2727, h7, hlam]
                                          · linarith only [h2498, h2727, hlam]
                                    · linarith only [h1, h2722, hlam]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h2203, h2204, h2510, h2512, h8, hlam, p2720_2]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    rcases p2720_3 (m.d 0 3) (by simp) with h2732 | h2732
                                    · rcases p2720_3 (m.d 1 3) (by simp) with h2733 | h2733
                                      · linarith only [h1, h2733, hlam]
                                      · rcases p2720_3 (m.d 2 3) (by simp) with h2735 | h2735
                                        · linarith only [h2735, h4, hlam]
                                        · rcases p2720_3 (m.d 3 4) (by simp) with h2737 | h2737
                                          · linarith only [h2737, hlam, p2720_0]
                                          · rcases p2720_3 (m.d 3 5) (by simp) with h2739 | h2739
                                            · linarith only [h2739, h8, hlam]
                                            · linarith only [h2516, h2739, hlam]
                                    · linarith only [h2732, hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h2203, h2204, h2510, h2512, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2720_1]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h1, hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h2498, hc23, hc34, hlam, hphi, p2720_1]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h2498, hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h2506, hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h4, hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h2202, hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h2510, hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h2512, hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h7, hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h7, h9, hc13, hc45, hlam, hphi, ht34, p2720_1]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h7, h9, hc23, hc45, hlam, hphi, ht34, p2720_1]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h2516, hlam, p2720_1]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h8, hlam, p2720_0]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    rcases p2720_3 (m.d 0 3) (by simp) with h2760 | h2760
                                    · rcases p2720_3 (m.d 1 3) (by simp) with h2761 | h2761
                                      · linarith only [h2761, hlam, p2720_0]
                                      · rcases p2720_3 (m.d 2 3) (by simp) with h2763 | h2763
                                        · linarith only [h2512, h2763, hlam]
                                        · rcases p2720_3 (m.d 3 4) (by simp) with h2765 | h2765
                                          · linarith only [h2516, h2765, hlam]
                                          · linarith only [h2498, h2765, hlam]
                                    · linarith only [h1, h2760, hlam]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    rcases p2720_3 (m.d 0 3) (by simp) with h2769 | h2769
                                    · rcases p2720_3 (m.d 1 3) (by simp) with h2770 | h2770
                                      · linarith only [h2506, h2770, hlam]
                                      · linarith only [h2202, h2770, hlam]
                                    · linarith only [h2769, h4, hlam]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [h2202, h2498, hc23, hc35, hlam, hphi, p2720_1]
                                  · have p2720_0 := h2720c.1
                                    have p2720_1 := h2720c.2.1
                                    have p2720_2 := h2720c.2.2.1
                                    have p2720_3 := h2720c.2.2.2
                                    linarith only [hlam, p2720_0]
                      · linarith only [h2541, hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h0, hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h0, h2202, h2204, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2518_1]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h0, h2204, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2518_1]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h2204, hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h1, hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h2202, hlam, p2518_1]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h2498, hlam, p2518_1]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h2506, hlam, p2518_1]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h2, hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h2203, hlam, p2518_1]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h2, h2202, h9, hc23, hc45, hlam, hphi, ht34, p2518_1]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h2508, hlam, p2518_1]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h3, hlam, p2518_0]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [h2202, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2518_1]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      rcases p2518_3 (m.d 0 1) (by simp) with h2794 | h2794
                      · rcases p2518_3 (m.d 1 2) (by simp) with h2795 | h2795
                        · linarith only [h2204, h2795, hlam]
                        · linarith only [h2202, h2795, hlam]
                      · linarith only [h1, h2794, hlam]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      rcases p2518_3 (m.d 0 1) (by simp) with h2799 | h2799
                      · rcases p2518_3 (m.d 1 2) (by simp) with h2800 | h2800
                        · linarith only [h2204, h2800, hlam]
                        · linarith only [h2203, h2800, hlam]
                      · linarith only [h2, h2799, hlam]
                    · have p2518_0 := h2518c.1
                      have p2518_1 := h2518c.2.1
                      have p2518_2 := h2518c.2.2.1
                      have p2518_3 := h2518c.2.2.2
                      linarith only [hlam, p2518_0]
  · linarith only [h2202, h2203, h5, h9, hc23, hc45, hlam, hphi, ht34]

end R2N4
