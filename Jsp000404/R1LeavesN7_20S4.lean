import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_20S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h2217 | h2217
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2218 | h2218
    · linarith only [h2, h2218, h3, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2220 | h2220
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2221 | h2221
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2222 | h2222
          · linarith only [h0, h2217, h2222, h3, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2224 | h2224
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2225 | h2225
              · linarith only [h0, h2218, h2221, h2225, h3, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2227 | h2227
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2228 | h2228
                  · linarith only [h2, h2225, h2228, h3, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2230 | h2230
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2231 | h2231
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2232 | h2232
                        · rcases h2bigk with h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c | h2233c
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2221, h2228, h2230, h2232, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2233_1]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2228, h2230, h2232, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2233_1]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h3, hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2228, h2230, h2232, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2233_1]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h0, hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2230, h2232, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2233_1]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2222, hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h0, h2228, h2230, h2232, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2233_1]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2, hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2221, hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2228, hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2, h2228, h2230, h2232, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2233_1]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2228, hc02, hc34, hlam, hphi, ht23, p2233_1]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2221, h2228, hc23, hc34, hlam, hphi, p2233_1]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2228, hc23, hc34, hlam, hphi, p2233_1]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            rcases p2233_3 (m.d 0 2) (by simp) with h2253 | h2253
                            · linarith only [h2253, h3, hlam]
                            · linarith only [h2217, h2253, hlam]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2217, hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2224, hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2230, hlam, p2233_1]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [h2231, hlam, p2233_0]
                          · have p2233_0 := h2233c.1
                            have p2233_1 := h2233c.2.1
                            have p2233_2 := h2233c.2.2.1
                            have p2233_3 := h2233c.2.2.2
                            linarith only [hlam, p2233_0]
                        · linarith only [h0, h2221, h2228, h2232, h3, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1, h2221, h2227, h2230, h2231, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
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
                            linarith only [h2224, h2230, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2265_1]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h3, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2265_1]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h3, hlam, p2265_0]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h2228, h2230, h3, hc23, hc34, hlam, hphi, p2265_1]
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
                            linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2265_1]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h2222, hlam, p2265_0]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h0, h2228, h2230, h3, hc23, hc34, hlam, hphi, p2265_1]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h2, hlam, p2265_0]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h2221, hlam, p2265_0]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [hlam, p2265_0]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h2228, hlam, p2265_0]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h2230, hlam, p2265_0]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h2228, hc02, hc34, hlam, hphi, ht23, p2265_1]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h2221, h2228, hc23, hc34, hlam, hphi, p2265_1]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h2228, hc23, hc34, hlam, hphi, p2265_1]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [hlam, p2265_0]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h2228, h2230, hc23, hc34, hlam, hphi, p2265_1]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h2217, hlam, p2265_0]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h2224, hlam, p2265_0]
                          · have p2265_0 := h2265c.1
                            have p2265_1 := h2265c.2.1
                            have p2265_2 := h2265c.2.2.1
                            have p2265_3 := h2265c.2.2.2
                            linarith only [h0, h2224, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2265_1]
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
                        · linarith only [h0, h2224, h2228, h2263, h2264, h3, hlam]
                      · linarith only [h2, h2263, h3, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h2218, h2220, h2221, h2222, h2227, hc23, hc34, hlam, hphi]
            · linarith only [h2217, h2221, h2224, h3, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
        · linarith only [h2, h2221, h3, hc12, hc24, hlam, hphi]
      · linarith only [h2217, h2220, h3, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2297 | h2297
    · linarith only [h2, h2297, h3, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2299 | h2299
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2300 | h2300
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2301 | h2301
          · linarith only [h0, h2301, h3, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2303 | h2303
            · linarith only [h0, h2217, h2303, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2305 | h2305
              · linarith only [h0, h2217, h2297, h2299, h2300, h2305, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2307 | h2307
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2308 | h2308
                  · linarith only [h2, h2305, h2308, h3, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2310 | h2310
                    · linarith only [h0, h2217, h2300, h2310, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2312 | h2312
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2313 | h2313
                        · rcases h2bigk with h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c | h2314c
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2217, h2308, h2312, hc12, hc34, hlam, hphi, ht23, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2217, h2308, h2312, hc23, hc34, hlam, hphi, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h3, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2217, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h0, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2301, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2303, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2300, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2308, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2310, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2308, hc02, hc34, hlam, hphi, ht23, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2300, h2308, hc23, hc34, hlam, hphi, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2308, hc23, hc34, hlam, hphi, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h0, h2217, h2300, h2308, hc23, hc34, hlam, hphi, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h0, h2300, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2300, h2310, hc23, hc35, hlam, hphi, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2310, hc23, hc35, hlam, hphi, p2314_1]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [h2312, hlam, p2314_0]
                          · have p2314_0 := h2314c.1
                            have p2314_1 := h2314c.2.1
                            have p2314_2 := h2314c.2.2.1
                            have p2314_3 := h2314c.2.2.2
                            linarith only [hlam, p2314_0]
                        · linarith only [h0, h2300, h2308, h2313, h3, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h2300, h2307, h2312, h3, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h2297, h2299, h2300, h2301, h2307, hc23, hc34, hlam, hphi]
        · linarith only [h2, h2217, h2300, hc12, hc25, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2344 | h2344
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2345 | h2345
          · linarith only [h0, h2345, h3, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2347 | h2347
            · linarith only [h0, h2217, h2347, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2349 | h2349
              · linarith only [h0, h2297, h2299, h2344, h2349, h3, hc03, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2351 | h2351
                · linarith only [h1, h2299, h2351, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2353 | h2353
                  · linarith only [h0, h2297, h2344, h2353, h3, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2355 | h2355
                    · linarith only [h0, h2217, h2344, h2355, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2357 | h2357
                      · linarith only [h0, h2299, h2344, h2353, h2357, h3, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2344, h2357, h3, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h2, h2344, h3, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
  · exact r1l7_22_14_H_I_L_I_s1_x0_x0 m hb2 hb4 hg0 hg1 h2 h3
  · exact r1l7_22_14_H_I_L_I_s1_x0_x1 m hb2 hb4 hg0 hg1 h2 h3

set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2361 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h2362 | h2362
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2363 | h2363
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2364 | h2364
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2365 | h2365
        · linarith only [h0, h2, h2361, h2365, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2367 | h2367
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2368 | h2368
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2369 | h2369
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2370 | h2370
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2371 | h2371
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2372 | h2372
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2373 | h2373
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2374 | h2374
                        · rcases h2bigk with h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c | h2375c
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [hlam, p2375_0]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2367, h2371, h2374, hc02, hc45, hlam, hphi, ht0b, ht5b, p2375_1]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2, hlam, p2375_0]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2, h2371, h2374, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2375_1]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2, h2372, h2374, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2375_1]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h0, hlam, p2375_0]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [hlam, p2375_0]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2365, hlam, p2375_0]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2371, h2374, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2375_1]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h0, h2, h2372, h2374, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2375_1]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p2375_1]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p2375_1]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [hlam, p2375_0]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2371, h2374, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2375_1]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            rcases p2375_3 (m.d 0 2) (by simp) with h2390 | h2390
                            · linarith only [h2, h2390, hlam]
                            · linarith only [h2362, h2390, hlam]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2361, hlam, p2375_0]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2367, hlam, p2375_0]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2371, hlam, p2375_1]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [hlam, p2375_0]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h0, h2367, h2372, h2374, hc02, hc45, hlam, hphi, ht0b, ht5b, p2375_1]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2362, hlam, p2375_0]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2368, hlam, p2375_0]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2372, hlam, p2375_1]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [h2373, hlam, p2375_0]
                          · have p2375_0 := h2375c.1
                            have p2375_1 := h2375c.2.1
                            have p2375_2 := h2375c.2.2.1
                            have p2375_3 := h2375c.2.2.2
                            linarith only [hlam, p2375_0]
                        · linarith only [h0, h2, h2367, h2373, h2374, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2404 | h2404
                        · linarith only [h2371, h2373, h2404, hlam]
                        · rcases h2bigk with h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c | h2406c
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2, hc12, hc23, hlam, hphi, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h0, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2365, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h0, h2, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            rcases p2406_3 (m.d 0 2) (by simp) with h2420 | h2420
                            · linarith only [h2, h2420, hlam]
                            · linarith only [h2361, h2420, hlam]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            rcases p2406_3 (m.d 0 2) (by simp) with h2423 | h2423
                            · linarith only [h2, h2423, hlam]
                            · linarith only [h2362, h2423, hlam]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2361, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2367, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2371, hlam, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2373, hlam, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2362, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2368, hlam, p2406_0]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2372, hlam, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [h2362, h2371, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2406_1]
                          · have p2406_0 := h2406c.1
                            have p2406_1 := h2406c.2.1
                            have p2406_2 := h2406c.2.2.1
                            have p2406_3 := h2406c.2.2.2
                            linarith only [hlam, p2406_0]
                    · linarith only [h0, h2, h2368, h2372, hlam]
                  · linarith only [h2, h2363, h2371, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2438 | h2438
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2439 | h2439
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2440 | h2440
                      · linarith only [h0, h2367, h2370, h2440, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2442 | h2442
                        · linarith only [h2367, h2370, h2438, h2442, hlam]
                        · rcases h2bigk with h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c | h2444c
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [hlam, p2444_0]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2, hc12, hc23, hlam, hphi, p2444_1]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2, hlam, p2444_0]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2, h2438, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2444_1]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2444_1]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h0, hlam, p2444_0]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [hlam, p2444_0]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2365, hlam, p2444_0]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h0, h2438, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2444_1]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h0, h2, h2439, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2444_1]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p2444_1]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p2444_1]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [hlam, p2444_0]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            rcases p2444_3 (m.d 0 2) (by simp) with h2458 | h2458
                            · linarith only [h2, h2458, hlam]
                            · linarith only [h2361, h2458, hlam]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            rcases p2444_3 (m.d 0 2) (by simp) with h2461 | h2461
                            · linarith only [h2, h2461, hlam]
                            · linarith only [h2362, h2461, hlam]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2361, hlam, p2444_0]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2367, hlam, p2444_0]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2438, hlam, p2444_1]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [hlam, p2444_0]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2440, hlam, p2444_1]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2362, hlam, p2444_0]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2368, hlam, p2444_0]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2439, hlam, p2444_1]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [h2368, h2438, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2444_1]
                          · have p2444_0 := h2444c.1
                            have p2444_1 := h2444c.2.1
                            have p2444_2 := h2444c.2.2.1
                            have p2444_3 := h2444c.2.2.2
                            linarith only [hlam, p2444_0]
                    · linarith only [h2, h2361, h2364, h2367, h2370, h2438, h2439, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h2, h2361, h2364, h2370, h2438, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h2365, h2367, h2369, hlam]
            · linarith only [h2, h2362, h2367, h2368, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h2, h2361, h2367, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2479 | h2479
        · linarith only [h0, h2, h2361, h2479, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2481 | h2481
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2482 | h2482
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2483 | h2483
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2484 | h2484
                · linarith only [h1, h2364, h2484, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2486 | h2486
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2487 | h2487
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2488 | h2488
                      · linarith only [h0, h2, h2364, h2481, h2488, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2490 | h2490
                        · linarith only [h1, h2364, h2481, h2486, h2490, hlam]
                        · rcases h2bigk with h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c | h2492c
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [hlam, p2492_0]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h2, hc12, hc23, hlam, hphi, p2492_1]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h2, hlam, p2492_0]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h2, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2492_1]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h2, h2486, h2488, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2492_1]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h0, hlam, p2492_0]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [hlam, p2492_0]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h2479, hlam, p2492_0]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h0, h2486, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2492_1]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h0, h2, h2486, h2488, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2492_1]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p2492_1]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p2492_1]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [hlam, p2492_0]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            rcases p2492_3 (m.d 0 2) (by simp) with h2506 | h2506
                            · linarith only [h2, h2506, hlam]
                            · linarith only [h2361, h2506, hlam]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            rcases p2492_3 (m.d 0 2) (by simp) with h2509 | h2509
                            · linarith only [h2, h2509, hlam]
                            · linarith only [h2362, h2509, hlam]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h2361, hlam, p2492_0]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h2481, hlam, p2492_0]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h2486, hlam, p2492_1]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [hlam, p2492_0]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h2488, hlam, p2492_1]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h2362, hlam, p2492_0]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h2482, hlam, p2492_0]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h2487, hlam, p2492_1]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [h0, h2482, h2486, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2492_1]
                          · have p2492_0 := h2492c.1
                            have p2492_1 := h2492c.2.1
                            have p2492_2 := h2492c.2.2.1
                            have p2492_3 := h2492c.2.2.2
                            linarith only [hlam, p2492_0]
                    · linarith only [h0, h2, h2482, h2487, hlam]
                  · linarith only [h2, h2363, h2486, hlam]
              · linarith only [h2363, h2364, h2479, h2481, h2483, hc24, hc45, hlam, hphi]
            · linarith only [h2, h2362, h2481, h2482, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h2, h2361, h2481, hc12, hc23, hlam, hphi]
    · linarith only [h2, h2361, h2363, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2528 | h2528
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2529 | h2529
      · linarith only [h2361, h2362, h2529, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2531 | h2531
        · linarith only [h0, h2, h2531, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2533 | h2533
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2534 | h2534
            · linarith only [h0, h2362, h2534, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2536 | h2536
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2537 | h2537
                · linarith only [h1, h2529, h2537, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2539 | h2539
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2540 | h2540
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2541 | h2541
                      · linarith only [h0, h2362, h2529, h2533, h2541, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2543 | h2543
                        · linarith only [h0, h2362, h2533, h2539, h2541, h2543, hlam]
                        · rcases h2bigk with h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c | h2545c
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [hlam, p2545_0]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2362, h2541, hc12, hc45, hlam, hphi, ht23, ht34, p2545_1]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2, hlam, p2545_0]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2362, h2539, h2541, hc34, hc45, hlam, hphi, p2545_1]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2362, hlam, p2545_0]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h0, hlam, p2545_0]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [hlam, p2545_0]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2531, hlam, p2545_0]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h0, h2539, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2545_1]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2534, hlam, p2545_0]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [hc02, hc23, hlam, hphi, p2545_1]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p2545_1]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [hlam, p2545_0]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            rcases p2545_3 (m.d 0 2) (by simp) with h2559 | h2559
                            · linarith only [h2, h2559, hlam]
                            · linarith only [h2361, h2559, hlam]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h0, h2362, h2533, h2539, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2545_1]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2361, hlam, p2545_0]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2533, hlam, p2545_0]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2539, hlam, p2545_1]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [hlam, p2545_0]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2541, hlam, p2545_1]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h0, h2533, h2539, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2545_1]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2533, h2539, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2545_1]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2540, hlam, p2545_1]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [h2539, h2541, hc34, hc45, hlam, hphi, p2545_1]
                          · have p2545_0 := h2545c.1
                            have p2545_1 := h2545c.2.1
                            have p2545_2 := h2545c.2.2.1
                            have p2545_3 := h2545c.2.2.2
                            linarith only [hlam, p2545_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2573 | h2573
                      · linarith only [h0, h2, h2533, h2540, h2573, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2575 | h2575
                        · linarith only [h0, h2, h2533, h2539, h2540, h2573, h2575, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h2, h2533, h2540, h2575, hc24, hc45, hlam, hphi]
                  · linarith only [h0, h2, h2528, h2533, h2539, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h2528, h2529, h2531, h2533, h2536, hc24, hc45, hlam, hphi]
          · linarith only [h2, h2361, h2533, hc12, hc23, hlam, hphi]
    · linarith only [h2, h2361, h2528, hlam]

set_option maxHeartbeats 6576000 in
theorem r1l7_22_14_H_I_L_I_s1_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2361 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h2582 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 4 (by decide) (by decide) with h2583 | h2583
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2584 | h2584
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2585 | h2585
      · linarith only [h0, h2, h2582, h2585, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2587 | h2587
        · linarith only [h0, h2361, h2587, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2589 | h2589
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2590 | h2590
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2591 | h2591
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2592 | h2592
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2593 | h2593
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2594 | h2594
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2595 | h2595
                      · rcases h2bigk with h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c | h2596c
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [hlam, p2596_0]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h2361, hc12, hc24, hlam, hphi, p2596_1]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h2, hlam, p2596_0]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h2361, hlam, p2596_0]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h2361, h2593, h2595, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2596_1]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h0, hlam, p2596_0]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [hlam, p2596_0]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h2585, hlam, p2596_0]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h2587, hlam, p2596_0]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h0, h2593, h2595, hc01, hc45, hlam, hphi, ht0b, ht5b, p2596_1]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p2596_1]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p2596_1]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [hlam, p2596_0]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h0, h2361, h2589, h2593, h2595, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2596_1]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          rcases p2596_3 (m.d 0 2) (by simp) with h2611 | h2611
                          · linarith only [h2, h2611, hlam]
                          · linarith only [h2582, h2611, hlam]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h0, h2589, h2593, h2595, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2596_1]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h2589, h2593, h2595, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2596_1]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h2592, hlam, p2596_1]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [hlam, p2596_0]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          rcases p2596_3 (m.d 0 2) (by simp) with h2618 | h2618
                          · linarith only [h2361, h2618, hlam]
                          · linarith only [h2582, h2618, hlam]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h2582, hlam, p2596_0]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h2589, hlam, p2596_0]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h2593, hlam, p2596_1]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [h2594, hlam, p2596_0]
                        · have p2596_0 := h2596c.1
                          have p2596_1 := h2596c.2.1
                          have p2596_2 := h2596c.2.2.1
                          have p2596_3 := h2596c.2.2.2
                          linarith only [hlam, p2596_0]
                      · rcases h2bigk with h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c | h2626c
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [hlam, p2626_0]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2589, h2594, h2595, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2626_1]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2, hlam, p2626_0]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2361, hlam, p2626_0]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2361, h2592, h2594, h2595, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2626_1]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h0, hlam, p2626_0]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [hlam, p2626_0]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2585, hlam, p2626_0]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2587, hlam, p2626_0]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2594, h2595, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2626_1]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p2626_1]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p2626_1]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [hlam, p2626_0]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2361, h2582, h2594, h2595, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2626_1]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2594, h2595, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2626_1]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h0, h2589, h2594, h2595, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2626_1]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2589, h2594, h2595, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2626_1]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2592, hlam, p2626_1]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [hlam, p2626_0]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2592, h2594, h2595, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2626_1]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2582, hlam, p2626_0]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2589, hlam, p2626_0]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2593, hlam, p2626_1]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [h2594, hlam, p2626_0]
                        · have p2626_0 := h2626c.1
                          have p2626_1 := h2626c.2.1
                          have p2626_2 := h2626c.2.2.1
                          have p2626_3 := h2626c.2.2.2
                          linarith only [hlam, p2626_0]
                    · linarith only [h2361, h2584, h2594, hlam]
                  · linarith only [h0, h2, h2589, h2593, hlam]
                · linarith only [h2, h2583, h2592, hlam]
              · linarith only [h2587, h2589, h2591, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2656 | h2656
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2657 | h2657
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2658 | h2658
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2659 | h2659
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2660 | h2660
                      · rcases h2bigk with h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c | h2661c
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [hlam, p2661_0]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2589, h2658, h2660, hc02, hc45, hlam, hphi, ht0b, ht5b, p2661_1]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2, hlam, p2661_0]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2361, hlam, p2661_0]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2, h2658, h2660, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2661_1]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h0, hlam, p2661_0]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [hlam, p2661_0]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2585, hlam, p2661_0]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2587, hlam, p2661_0]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2585, h2590, h2658, h2660, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2661_1]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p2661_1]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p2661_1]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [hlam, p2661_0]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h0, h2361, h2589, h2658, h2660, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2661_1]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          rcases p2661_3 (m.d 0 2) (by simp) with h2676 | h2676
                          · linarith only [h2, h2676, hlam]
                          · linarith only [h2582, h2676, hlam]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h0, h2589, h2658, h2660, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2661_1]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2589, h2658, h2660, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2661_1]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2657, hlam, p2661_1]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [hlam, p2661_0]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          rcases p2661_3 (m.d 0 2) (by simp) with h2683 | h2683
                          · linarith only [h2361, h2683, hlam]
                          · linarith only [h2582, h2683, hlam]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2582, hlam, p2661_0]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2589, hlam, p2661_0]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2658, hlam, p2661_1]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [h2659, hlam, p2661_0]
                        · have p2661_0 := h2661c.1
                          have p2661_1 := h2661c.2.1
                          have p2661_2 := h2661c.2.2.1
                          have p2661_3 := h2661c.2.2.2
                          linarith only [hlam, p2661_0]
                      · linarith only [h2584, h2585, h2589, h2590, h2660, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h2361, h2589, h2656, h2659, hlam]
                  · linarith only [h2, h2583, h2585, h2589, h2590, h2658, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h2, h2583, h2657, hlam]
              · linarith only [h2585, h2589, h2590, h2656, hlam]
          · linarith only [h2, h2582, h2589, hc12, hc23, hlam, hphi]
    · linarith only [h2361, h2582, h2584, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2698 | h2698
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2699 | h2699
      · linarith only [h0, h2, h2582, h2699, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2701 | h2701
        · linarith only [h0, h2361, h2701, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2703 | h2703
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2704 | h2704
            · linarith only [h1, h2583, h2704, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2706 | h2706
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2707 | h2707
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2708 | h2708
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2709 | h2709
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2710 | h2710
                      · rcases h2bigk with h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c | h2711c
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [hlam, p2711_0]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2703, h2708, h2710, hc02, hc45, hlam, hphi, ht0b, ht5b, p2711_1]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2, hlam, p2711_0]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2361, hlam, p2711_0]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2, h2583, h2708, h2710, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2711_1]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h0, hlam, p2711_0]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [hlam, p2711_0]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2699, hlam, p2711_0]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2701, hlam, p2711_0]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h0, h2708, h2710, hc01, hc45, hlam, hphi, ht0b, ht5b, p2711_1]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [hc02, hc23, hlam, hphi, p2711_1]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p2711_1]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [hlam, p2711_0]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2361, h2582, h2708, h2710, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2711_1]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          rcases p2711_3 (m.d 0 2) (by simp) with h2726 | h2726
                          · linarith only [h2, h2726, hlam]
                          · linarith only [h2582, h2726, hlam]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h0, h2703, h2708, h2710, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2711_1]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2703, h2708, h2710, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2711_1]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2707, hlam, p2711_1]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [hlam, p2711_0]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          rcases p2711_3 (m.d 0 2) (by simp) with h2733 | h2733
                          · linarith only [h2361, h2733, hlam]
                          · linarith only [h2582, h2733, hlam]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2582, hlam, p2711_0]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2703, hlam, p2711_0]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2708, hlam, p2711_1]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [h2709, hlam, p2711_0]
                        · have p2711_0 := h2711c.1
                          have p2711_1 := h2711c.2.1
                          have p2711_2 := h2711c.2.2.1
                          have p2711_3 := h2711c.2.2.2
                          linarith only [hlam, p2711_0]
                      · linarith only [h2583, h2698, h2710, hlam]
                    · linarith only [h2361, h2698, h2709, hlam]
                  · linarith only [h2, h2583, h2707, h2708, hc02, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2744 | h2744
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2745 | h2745
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2746 | h2746
                      · rcases h2bigk with h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c | h2747c
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2703, h2744, h2746, hc02, hc45, hlam, hphi, ht0b, ht5b, p2747_1]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2, hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2361, hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2, h2707, h2744, h2746, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2747_1]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h0, hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2699, hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2701, hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h0, h2744, h2746, hc01, hc45, hlam, hphi, ht0b, ht5b, p2747_1]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2707, hc02, hc34, hlam, hphi, ht23, p2747_1]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2707, hc12, hc34, hlam, hphi, ht23, p2747_1]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2707, hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2707, h2744, h2746, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2747_1]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h0, h2703, h2707, h2744, h2746, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2747_1]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2703, h2707, h2744, h2746, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2747_1]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2, h2707, hc03, hc34, hlam, hphi, p2747_1]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          rcases p2747_3 (m.d 0 2) (by simp) with h2767 | h2767
                          · linarith only [h2361, h2767, hlam]
                          · linarith only [h2582, h2767, hlam]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2582, hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2703, hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2744, hlam, p2747_1]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [h2745, hlam, p2747_0]
                        · have p2747_0 := h2747c.1
                          have p2747_1 := h2747c.2.1
                          have p2747_2 := h2747c.2.2.1
                          have p2747_3 := h2747c.2.2.2
                          linarith only [hlam, p2747_0]
                      · linarith only [h2361, h2698, h2707, h2746, hlam]
                    · linarith only [h0, h2, h2703, h2706, h2707, h2745, hlam]
                  · linarith only [h0, h2, h2703, h2744, hlam]
              · linarith only [h2699, h2703, h2704, h2706, hlam]
          · linarith only [h2, h2582, h2703, hc12, hc23, hlam, hphi]
    · linarith only [h2, h2582, h2583, h2698, hlam]

end R2N4
