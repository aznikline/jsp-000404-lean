import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_31S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h2259 | h2259
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2260 | h2260
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2261 | h2261
      · linarith only [h0, h2259, h2261, h3, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2263 | h2263
        · linarith only [h0, h2263, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2265 | h2265
          · linarith only [h1, h2263, h2265, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
          · linarith only [h0, h2259, h2265, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2268 | h2268
      · linarith only [h0, h2259, h2268, h3, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2270 | h2270
        · linarith only [h0, h2270, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2272 | h2272
          · linarith only [h1, h2270, h2272, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
          · linarith only [h0, h2259, h2272, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2275 | h2275
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2276 | h2276
      · linarith only [h1, h2275, h2276, h3, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2278 | h2278
        · linarith only [h0, h2278, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2280 | h2280
          · linarith only [h1, h2259, h2278, h2280, h3, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2282 | h2282
            · linarith only [h0, h2282, h3, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2284 | h2284
              · linarith only [h1, h2284, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
              · linarith only [h1, h2275, h2284, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2287 | h2287
      · linarith only [h2, h2287, h3, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2289 | h2289
        · linarith only [h0, h2289, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2291 | h2291
          · linarith only [h1, h2259, h2289, h2291, h3, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2293 | h2293
            · linarith only [h0, h2293, h3, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2295 | h2295
              · linarith only [h1, h2275, h2295, h3, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2297 | h2297
                · linarith only [h2, h2295, h2297, h3, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2299 | h2299
                  · linarith only [h2, h2287, h2299, h3, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2301 | h2301
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2302 | h2302
                      · linarith only [h2, h2289, h2295, h2299, h2302, h3, hc12, hc24, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2304 | h2304
                        · linarith only [h0, h2259, h2302, h2304, hc12, hc34, hlam, hphi, ht23]
                        · rcases h1bigk with h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c | h2306c
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [hlam, p2306_0]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2306_1, u1elo4]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2306_1, u1elo4]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2306_1, u1elo4]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h3, hlam, p2306_0]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h0, hlam, p2306_0]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [hlam, p2306_0]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h2289, hlam, p2306_1]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h2291, hlam, p2306_1]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h2293, hlam, p2306_1]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h1, hlam, p2306_0]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h1, h2275, h2301, hc12, hc24, hlam, hphi, p2306_1]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [hlam, p2306_0]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h2295, hlam, p2306_0]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h2297, hlam, p2306_1]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h2, hlam, p2306_0]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h2, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2306_1, u1elo4]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h2, h2289, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2306_1, u1elo4]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [hlam, p2306_0]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [h2299, hlam, p2306_1]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [hc01, hlam, hphi, p2306_1, u1elo4]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            rcases p2306_3 (m.d 0 1) (by simp) with h2328 | h2328
                            · linarith only [h2328, h3, hlam]
                            · linarith only [h0, h2328, hlam]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            rcases p2306_3 (m.d 0 1) (by simp) with h2331 | h2331
                            · linarith only [h2331, h3, hlam]
                            · linarith only [h1, h2331, hlam]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            rcases p2306_3 (m.d 0 1) (by simp) with h2334 | h2334
                            · linarith only [h2334, h3, hlam]
                            · linarith only [h2, h2334, hlam]
                          · have p2306_0 := h2306c.1
                            have p2306_1 := h2306c.2.1
                            have p2306_2 := h2306c.2.2.1
                            have p2306_3 := h2306c.2.2.2
                            linarith only [hlam, p2306_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2338 | h2338
                      · linarith only [h2, h2289, h2295, h2299, h2338, h3, hc12, hc24, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2340 | h2340
                        · linarith only [h0, h2259, h2338, h2340, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h2289, h2301, h2340, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_21_14_M_LI_L_I_s0_x0_x0_x0 m hb1 hb4 hg0 h1 h2 h3
  · exact r1l7_21_14_M_LI_L_I_s0_x0_x0_x1 m hb1 hb4 hg0 h1 h2 h3

set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h2343 | h2343
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2344 | h2344
    · linarith only [h0, h2, h2344, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2346 | h2346
      · linarith only [h1, h2, h2346, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2348 | h2348
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2349 | h2349
          · linarith only [h0, h2, h2349, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2351 | h2351
            · linarith only [h1, h2, h2344, h2349, h2351, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2353 | h2353
              · linarith only [h0, h2, h2353, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2355 | h2355
                · linarith only [h1, h2, h2346, h2355, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2357 | h2357
                  · linarith only [h1, h2, h2357, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2359 | h2359
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2360 | h2360
                      · linarith only [h2, h2343, h2349, h2355, h2357, h2360, hc12, hc23, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2362 | h2362
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2363 | h2363
                          · rcases h1bigk with h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c | h2364c
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [hlam, p2364_0]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2364_1, u1elo3]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2364_1, u1elo3]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2, hlam, p2364_0]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p2364_1, u1elo3]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h0, hlam, p2364_0]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [hlam, p2364_0]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2349, hlam, p2364_1]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2351, hlam, p2364_1]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2353, hlam, p2364_1]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h1, hlam, p2364_0]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2357, hc12, hc35, hlam, hphi, ht23, p2364_1]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [hlam, p2364_0]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2355, hlam, p2364_0]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2357, hlam, p2364_1]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [hc01, hlam, hphi, p2364_1, u1elo3]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              rcases p2364_3 (m.d 0 1) (by simp) with h2381 | h2381
                              · linarith only [h2, h2381, hlam]
                              · linarith only [h0, h2381, hlam]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              rcases p2364_3 (m.d 0 1) (by simp) with h2384 | h2384
                              · linarith only [h2, h2384, hlam]
                              · linarith only [h1, h2384, hlam]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [hlam, p2364_0]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              rcases p2364_3 (m.d 0 1) (by simp) with h2388 | h2388
                              · linarith only [h2, h2388, hlam]
                              · linarith only [h2343, h2388, hlam]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2343, hlam, p2364_0]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2343, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2364_1, u1elo0]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2, h2343, h2349, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2364_1, u1elo3]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [h2359, hlam, p2364_0]
                            · have p2364_0 := h2364c.1
                              have p2364_1 := h2364c.2.1
                              have p2364_2 := h2364c.2.2.1
                              have p2364_3 := h2364c.2.2.2
                              linarith only [hlam, p2364_0]
                          · linarith only [h0, h2, h2351, h2360, h2363, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h2, h2343, h2351, h2359, h2362, hlam]
                    · linarith only [h2, h2343, h2349, h2357, h2359, hc12, hc45, hlam, hphi, ht23, ht34]
        · linarith only [h2, h2343, h2348, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2400 | h2400
    · linarith only [h0, h2, h2400, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2402 | h2402
      · linarith only [h1, h2, h2402, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2404 | h2404
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2405 | h2405
          · linarith only [h0, h2, h2405, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2407 | h2407
            · linarith only [h1, h2, h2400, h2405, h2407, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2409 | h2409
              · linarith only [h1, h2, h2405, h2409, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2411 | h2411
                · linarith only [h1, h2, h2402, h2411, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2413 | h2413
                  · linarith only [h1, h2, h2413, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2415 | h2415
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2416 | h2416
                      · linarith only [h1, h2343, h2405, h2411, h2415, h2416, hc12, hc23, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2418 | h2418
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2419 | h2419
                          · rcases h1bigk with h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c | h2420c
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [hlam, p2420_0]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h2343, h2415, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2420_1, u1elo3]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h2343, h2415, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2420_1, u1elo3]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h2, hlam, p2420_0]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h2343, hlam, p2420_0]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h0, hlam, p2420_0]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [hlam, p2420_0]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h2405, hlam, p2420_1]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h2407, hlam, p2420_1]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h2409, hlam, p2420_1]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h1, hlam, p2420_0]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h1, h2343, h2415, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2420_1, u1elo3]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [hlam, p2420_0]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h2411, hlam, p2420_0]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h2413, hlam, p2420_1]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [hc01, hlam, hphi, p2420_1, u1elo3]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              rcases p2420_3 (m.d 0 1) (by simp) with h2437 | h2437
                              · linarith only [h2, h2437, hlam]
                              · linarith only [h0, h2437, hlam]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              rcases p2420_3 (m.d 0 1) (by simp) with h2440 | h2440
                              · linarith only [h2, h2440, hlam]
                              · linarith only [h1, h2440, hlam]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [hlam, p2420_0]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h1, h2343, h2405, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2420_1, u1elo3]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h1, h2405, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2420_1, u1elo4]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              rcases p2420_3 (m.d 0 1) (by simp) with h2446 | h2446
                              · linarith only [h2343, h2446, hlam]
                              · linarith only [h0, h2446, hlam]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              rcases p2420_3 (m.d 0 1) (by simp) with h2449 | h2449
                              · linarith only [h2343, h2449, hlam]
                              · linarith only [h1, h2449, hlam]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [h2415, hlam, p2420_0]
                            · have p2420_0 := h2420c.1
                              have p2420_1 := h2420c.2.1
                              have p2420_2 := h2420c.2.2.1
                              have p2420_3 := h2420c.2.2.2
                              linarith only [hlam, p2420_0]
                          · linarith only [h1, h2, h2404, h2405, h2407, h2416, h2419, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h2, h2404, h2407, h2418, hlam]
                    · linarith only [h2, h2404, h2415, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2457 | h2457
          · linarith only [h0, h2, h2457, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2459 | h2459
            · linarith only [h1, h2, h2457, h2459, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2461 | h2461
              · linarith only [h1, h2, h2457, h2461, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2463 | h2463
                · linarith only [h1, h2, h2463, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2465 | h2465
                  · linarith only [h1, h2, h2465, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2467 | h2467
                    · linarith only [h2, h2404, h2467, hc01, hlam, hphi, u1elo3]
                    · linarith only [h1, h2, h2457, h2467, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_21_14_M_LI_L_I_s0_x0_x0 m hb1 hb4 hg0 h1 h2
  · exact r1l7_21_14_M_LI_L_I_s0_x0_x1 m hb1 hb4 hg0 h1 h2

set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h2470 | h2470
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2471 | h2471
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2472 | h2472
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2473 | h2473
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2474 | h2474
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2475 | h2475
            · linarith only [h0, h1, h2475, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2477 | h2477
              · linarith only [h0, h1, h2477, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · linarith only [h0, h1, h2472, h2477, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2480 | h2480
            · linarith only [h0, h1, h2480, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2482 | h2482
              · linarith only [h0, h1, h2482, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · linarith only [h0, h1, h2472, h2482, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
        · linarith only [h0, h1, h2472, h2473, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2486 | h2486
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2487 | h2487
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2488 | h2488
            · linarith only [h0, h1, h2488, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2490 | h2490
              · linarith only [h0, h1, h2472, h2490, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2492 | h2492
                · linarith only [h0, h1, h2492, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2494 | h2494
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2495 | h2495
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2496 | h2496
                      · linarith only [h1, h2470, h2496, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · linarith only [h1, h2470, h2487, h2490, h2496, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h0, h1, h2495, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h2470, h2486, h2490, h2494, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2501 | h2501
            · linarith only [h0, h1, h2501, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2503 | h2503
              · linarith only [h0, h1, h2472, h2503, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2505 | h2505
                · linarith only [h0, h1, h2505, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2507 | h2507
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2508 | h2508
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2509 | h2509
                      · linarith only [h1, h2470, h2487, h2509, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2511 | h2511
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2512 | h2512
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2513 | h2513
                            · linarith only [h2470, h2487, h2507, h2513, hlam]
                            · rcases h1bigk with h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c | h2515c
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2515_1, u1elo2]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h1, hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h1, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2515_1, u1elo2]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p2515_1, u1elo2]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h0, hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2501, hlam, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2503, hlam, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2505, hlam, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [hc01, hlam, hphi, p2515_1, u1elo2]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                rcases p2515_3 (m.d 0 1) (by simp) with h2527 | h2527
                                · linarith only [h1, h2527, hlam]
                                · linarith only [h0, h2527, hlam]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                rcases p2515_3 (m.d 0 1) (by simp) with h2531 | h2531
                                · linarith only [h1, h2531, hlam]
                                · linarith only [h2470, h2531, hlam]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                rcases p2515_3 (m.d 0 1) (by simp) with h2534 | h2534
                                · linarith only [h1, h2534, hlam]
                                · linarith only [h2471, h2534, hlam]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2470, hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2471, h2509, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2515_1, u1elo0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2507, hlam, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2509, hlam, p2515_1]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2471, hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h1, h2471, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2515_1, u1elo2]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h2508, hlam, p2515_0]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [h1, h2471, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2515_1, u1elo2]
                              · have p2515_0 := h2515c.1
                                have p2515_1 := h2515c.2.1
                                have p2515_2 := h2515c.2.2.1
                                have p2515_3 := h2515c.2.2.2
                                linarith only [hlam, p2515_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2547 | h2547
                            · linarith only [h0, h2472, h2512, h2547, hc12, hc34, hlam, hphi, ht23]
                            · rcases h1bigk with h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c | h2549c
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [hlam, p2549_0]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2549_1, u1elo2]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h1, hlam, p2549_0]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h1, h2503, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2549_1, u1elo2]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p2549_1, u1elo2]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h0, hlam, p2549_0]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [hlam, p2549_0]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h2501, hlam, p2549_1]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h2503, hlam, p2549_1]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h2505, hlam, p2549_1]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [hc01, hlam, hphi, p2549_1, u1elo2]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                rcases p2549_3 (m.d 0 1) (by simp) with h2561 | h2561
                                · linarith only [h1, h2561, hlam]
                                · linarith only [h0, h2561, hlam]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [hlam, p2549_0]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                rcases p2549_3 (m.d 0 1) (by simp) with h2565 | h2565
                                · linarith only [h1, h2565, hlam]
                                · linarith only [h2470, h2565, hlam]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                rcases p2549_3 (m.d 0 1) (by simp) with h2568 | h2568
                                · linarith only [h1, h2568, hlam]
                                · linarith only [h2471, h2568, hlam]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h2470, hlam, p2549_0]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h1, h2470, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2549_1, u1elo2]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h2507, hlam, p2549_1]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [hlam, p2549_0]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h2509, hlam, p2549_1]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h2471, hlam, p2549_0]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h1, h2471, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2549_1, u1elo2]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h2508, hlam, p2549_0]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [h1, h2471, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2549_1, u1elo2]
                              · have p2549_0 := h2549c.1
                                have p2549_1 := h2549c.2.1
                                have p2549_2 := h2549c.2.2.1
                                have p2549_3 := h2549c.2.2.2
                                linarith only [hlam, p2549_0]
                        · linarith only [h0, h1, h2501, h2511, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h2470, h2503, h2508, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h2470, h2503, h2507, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1, h2470, h2486, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2585 | h2585
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2586 | h2586
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2587 | h2587
          · linarith only [h0, h2471, h2585, h2587, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2589 | h2589
            · linarith only [h0, h1, h2589, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2591 | h2591
              · linarith only [h0, h1, h2591, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · linarith only [h0, h1, h2585, h2591, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
        · linarith only [h0, h1, h2585, h2586, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2595 | h2595
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2596 | h2596
          · linarith only [h2470, h2471, h2596, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2598 | h2598
            · linarith only [h0, h1, h2598, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2600 | h2600
              · linarith only [h0, h1, h2585, h2600, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2602 | h2602
                · linarith only [h0, h1, h2602, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2604 | h2604
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2605 | h2605
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2606 | h2606
                      · linarith only [h2470, h2471, h2596, h2605, h2606, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2608 | h2608
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2609 | h2609
                          · linarith only [h2470, h2471, h2600, h2606, h2609, hc12, hc24, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2611 | h2611
                            · linarith only [h2470, h2471, h2604, h2605, h2609, h2611, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · rcases h1bigk with h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c | h2613c
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [hlam, p2613_0]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h2471, h2605, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2613_1, u1elo2]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h1, hlam, p2613_0]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h2471, h2605, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2613_1, u1elo2]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h2471, hlam, p2613_0]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h0, hlam, p2613_0]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [hlam, p2613_0]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h2598, hlam, p2613_1]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h2600, hlam, p2613_1]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h2602, hlam, p2613_1]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [hc01, hlam, hphi, p2613_1, u1elo2]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                rcases p2613_3 (m.d 0 1) (by simp) with h2625 | h2625
                                · linarith only [h1, h2625, hlam]
                                · linarith only [h0, h2625, hlam]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [hlam, p2613_0]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                rcases p2613_3 (m.d 0 1) (by simp) with h2629 | h2629
                                · linarith only [h1, h2629, hlam]
                                · linarith only [h2470, h2629, hlam]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h2470, h2471, h2600, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2613_1, u1elo2]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h2470, hlam, p2613_0]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h2470, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2613_1, u1elo0]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h2604, hlam, p2613_1]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [hlam, p2613_0]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h2606, hlam, p2613_1]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [hc01, hlam, hphi, p2613_1, u1elo4]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                rcases p2613_3 (m.d 0 1) (by simp) with h2639 | h2639
                                · linarith only [h2471, h2639, hlam]
                                · linarith only [h0, h2639, hlam]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [h2605, hlam, p2613_0]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                rcases p2613_3 (m.d 0 1) (by simp) with h2643 | h2643
                                · linarith only [h2471, h2643, hlam]
                                · linarith only [h2470, h2643, hlam]
                              · have p2613_0 := h2613c.1
                                have p2613_1 := h2613c.2.1
                                have p2613_2 := h2613c.2.2.1
                                have p2613_3 := h2613c.2.2.2
                                linarith only [hlam, p2613_0]
                        · linarith only [h1, h2595, h2598, h2608, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h1, h2470, h2600, h2605, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h2470, h2600, h2604, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1, h2470, h2595, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2651 | h2651
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2652 | h2652
      · linarith only [h0, h2470, h2652, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2654 | h2654
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2655 | h2655
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2656 | h2656
            · linarith only [h0, h1, h2656, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2658 | h2658
              · linarith only [h0, h1, h2652, h2658, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2660 | h2660
                · linarith only [h0, h1, h2660, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2662 | h2662
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2663 | h2663
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2664 | h2664
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2665 | h2665
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2666 | h2666
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2667 | h2667
                            · rcases h1bigk with h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c | h2668c
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [hlam, p2668_0]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2470, h2662, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2668_1, u1elo2]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h1, hlam, p2668_0]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2470, hlam, p2668_0]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2470, h2662, hc15, hlam, hphi, ht01, ht0b, ht5b, p2668_1, u1elo2]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h0, hlam, p2668_0]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [hlam, p2668_0]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2656, hlam, p2668_1]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2658, hlam, p2668_1]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2660, hlam, p2668_1]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [hc01, hlam, hphi, p2668_1, u1elo2]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                rcases p2668_3 (m.d 0 1) (by simp) with h2680 | h2680
                                · linarith only [h1, h2680, hlam]
                                · linarith only [h0, h2680, hlam]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [hlam, p2668_0]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2470, h2651, h2660, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2668_1, u1elo2]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                rcases p2668_3 (m.d 0 1) (by simp) with h2685 | h2685
                                · linarith only [h1, h2685, hlam]
                                · linarith only [h2651, h2685, hlam]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2651, h2660, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2668_1, u1elo3]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                rcases p2668_3 (m.d 0 1) (by simp) with h2689 | h2689
                                · linarith only [h2470, h2689, hlam]
                                · linarith only [h0, h2689, hlam]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2662, hlam, p2668_1]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [hlam, p2668_0]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                rcases p2668_3 (m.d 0 1) (by simp) with h2694 | h2694
                                · linarith only [h2470, h2694, hlam]
                                · linarith only [h2651, h2694, hlam]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2651, hlam, p2668_0]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2651, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2668_1, u1elo0]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2663, hlam, p2668_0]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [h2664, hlam, p2668_0]
                              · have p2668_0 := h2668c.1
                                have p2668_1 := h2668c.2.1
                                have p2668_2 := h2668c.2.2.1
                                have p2668_3 := h2668c.2.2.2
                                linarith only [hlam, p2668_0]
                            · linarith only [h2470, h2651, h2662, h2664, h2667, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · linarith only [h2470, h2651, h2658, h2664, h2666, hlam]
                        · linarith only [h0, h2470, h2656, h2662, h2665, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h2470, h2651, h2660, h2664, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h2470, h2651, h2660, h2662, h2663, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h2651, h2654, h2660, h2662, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h2470, h2651, h2655, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2709 | h2709
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2710 | h2710
            · linarith only [h0, h2470, h2710, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2712 | h2712
              · linarith only [h0, h2470, h2712, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2714 | h2714
                · linarith only [h0, h2470, h2714, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2716 | h2716
                  · linarith only [h1, h2651, h2654, h2714, h2716, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · linarith only [h1, h2651, h2714, h2716, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h1, h2651, h2654, h2709, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2720 | h2720
      · linarith only [h0, h2470, h2720, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2722 | h2722
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2723 | h2723
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2724 | h2724
            · linarith only [h0, h1, h2724, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2726 | h2726
              · linarith only [h0, h1, h2720, h2726, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2728 | h2728
                · linarith only [h0, h1, h2728, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2730 | h2730
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2731 | h2731
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2732 | h2732
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2733 | h2733
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2734 | h2734
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2735 | h2735
                            · rcases h1bigk with h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c | h2736c
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [hlam, p2736_0]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h2651, h2730, h2732, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2736_1, u1elo2]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h1, hlam, p2736_0]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h2470, hlam, p2736_0]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h2651, hlam, p2736_0]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h0, hlam, p2736_0]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [hlam, p2736_0]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h2724, hlam, p2736_1]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h2726, hlam, p2736_1]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h2728, hlam, p2736_1]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [hc01, hlam, hphi, p2736_1, u1elo2]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                rcases p2736_3 (m.d 0 1) (by simp) with h2748 | h2748
                                · linarith only [h1, h2748, hlam]
                                · linarith only [h0, h2748, hlam]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [hlam, p2736_0]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h0, h2470, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2736_1, u1elo2]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h0, h2651, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2736_1, u1elo2]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2736_1, u1elo3]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                rcases p2736_3 (m.d 0 1) (by simp) with h2755 | h2755
                                · linarith only [h2470, h2755, hlam]
                                · linarith only [h0, h2755, hlam]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h2730, hlam, p2736_1]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [hlam, p2736_0]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h0, h2651, h2730, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2736_1, u1elo2]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2736_1, u1elo4]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                rcases p2736_3 (m.d 0 1) (by simp) with h2762 | h2762
                                · linarith only [h2651, h2762, hlam]
                                · linarith only [h0, h2762, hlam]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h2731, hlam, p2736_0]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [h2732, hlam, p2736_0]
                              · have p2736_0 := h2736c.1
                                have p2736_1 := h2736c.2.1
                                have p2736_2 := h2736c.2.2.1
                                have p2736_3 := h2736c.2.2.2
                                linarith only [hlam, p2736_0]
                            · rcases h1bigk with h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c | h2768c
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [hlam, p2768_0]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2768_1, u1elo2]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h1, hlam, p2768_0]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h2470, hlam, p2768_0]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h2651, hlam, p2768_0]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h0, hlam, p2768_0]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [hlam, p2768_0]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h2724, hlam, p2768_1]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h2726, hlam, p2768_1]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h2728, hlam, p2768_1]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [hc01, hlam, hphi, p2768_1, u1elo2]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                rcases p2768_3 (m.d 0 1) (by simp) with h2780 | h2780
                                · linarith only [h1, h2780, hlam]
                                · linarith only [h0, h2780, hlam]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [hlam, p2768_0]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h2470, h2723, h2735, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2768_1, u1elo2]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h0, h2651, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2768_1, u1elo2]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2768_1, u1elo3]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                rcases p2768_3 (m.d 0 1) (by simp) with h2787 | h2787
                                · linarith only [h2470, h2787, hlam]
                                · linarith only [h0, h2787, hlam]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h2730, hlam, p2768_1]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [hlam, p2768_0]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h0, h2651, h2730, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2768_1, u1elo2]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2768_1, u1elo4]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                rcases p2768_3 (m.d 0 1) (by simp) with h2794 | h2794
                                · linarith only [h2651, h2794, hlam]
                                · linarith only [h0, h2794, hlam]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h2731, hlam, p2768_0]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [h2732, hlam, p2768_0]
                              · have p2768_0 := h2768c.1
                                have p2768_1 := h2768c.2.1
                                have p2768_2 := h2768c.2.2.1
                                have p2768_3 := h2768c.2.2.2
                                linarith only [hlam, p2768_0]
                          · linarith only [h0, h1, h2470, h2722, h2723, h2726, h2734, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · linarith only [h0, h1, h2724, h2733, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h2470, h2722, h2723, h2732, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1, h2731, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h2722, h2730, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2805 | h2805
            · linarith only [h0, h1, h2805, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2807 | h2807
              · linarith only [h0, h1, h2807, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2809 | h2809
                · linarith only [h0, h1, h2809, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2811 | h2811
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2812 | h2812
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2813 | h2813
                      · linarith only [h2470, h2723, h2811, h2813, hc01, hlam, hphi, u1elo2]
                      · linarith only [h0, h2470, h2813, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h0, h1, h2812, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h2722, h2811, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2818 | h2818
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2819 | h2819
            · linarith only [h0, h1, h2819, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2821 | h2821
              · linarith only [h0, h1, h2821, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2823 | h2823
                · linarith only [h0, h1, h2823, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2825 | h2825
                  · linarith only [h1, h2722, h2825, hc01, hlam, hphi, u1elo2]
                  · linarith only [h0, h1, h2825, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2828 | h2828
            · linarith only [h0, h1, h2828, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2830 | h2830
              · linarith only [h0, h1, h2830, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2832 | h2832
                · linarith only [h0, h1, h2832, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2834 | h2834
                  · linarith only [h1, h2722, h2834, hc01, hlam, hphi, u1elo2]
                  · linarith only [h0, h1, h2834, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_21_14_M_LI_L_I_s0_x0 m hb1 hb4 hg0 h1
  · exact r1l7_21_14_M_LI_L_I_s0_x1 m hb1 hb4 hg0 h1

set_option maxHeartbeats 9486000 in
set_option maxHeartbeats 9486000 in
theorem r1l7_21_14_M_LI_L_I_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  exact r1l7_21_14_M_LI_L_I_s0 m hb1 hb4 h0

end R2N4
