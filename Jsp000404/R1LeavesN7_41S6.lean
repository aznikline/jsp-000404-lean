import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1741 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h2261 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h2262 | h2262
  · rcases m.htr 1 3 5 (by decide) (by decide) with h2263 | h2263
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2264 | h2264
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2265 | h2265
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2266 | h2266
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2267 | h2267
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2268 | h2268
              · rcases h5bigk with h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c | h2269c
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [hlam, p2269_0]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h0, hlam, p2269_1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h1741, hlam, p2269_0]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h1741, h2262, hc35, hlam, hphi, ht01, ht0b, ht5b, p2269_1, u1elo1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h1741, h2262, hc45, hlam, hphi, ht01, ht0b, ht5b, p2269_1, u1elo1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2263, hc05, hlam, hphi, ht01, ht0b, ht5b, p2269_1, u1elo2]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [hlam, p2269_0]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h1741, h2263, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2269_1, u1elo2]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2263, hc35, hlam, hphi, ht01, ht0b, ht5b, p2269_1, u1elo2]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2263, hc45, hlam, hphi, ht01, ht0b, ht5b, p2269_1, u1elo2]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2269_1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2262, hlam, p2269_1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [hlam, p2269_0]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2262, hc35, hlam, hphi, ht01, ht0b, ht5b, p2269_1, u1elo1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2262, hc45, hlam, hphi, ht01, ht0b, ht5b, p2269_1, u1elo1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2269_1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2263, hlam, p2269_1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2266, hlam, p2269_0]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [hlam, p2269_0]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2262, h2266, hc45, hlam, hphi, ht01, ht0b, ht5b, p2269_1, u1elo1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2261, hlam, p2269_1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2264, hlam, p2269_1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2267, hlam, p2269_1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [h2268, hlam, p2269_1]
                · have p2269_0 := h2269c.1
                  have p2269_1 := h2269c.2.1
                  have p2269_2 := h2269c.2.2.1
                  have p2269_3 := h2269c.2.2.2
                  linarith only [hlam, p2269_0]
              · rcases h5bigk with h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c | h2295c
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [hlam, p2295_0]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h0, hlam, p2295_1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h1741, hlam, p2295_0]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h1741, h2262, hc35, hlam, hphi, ht01, ht0b, ht5b, p2295_1, u1elo1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h1741, h2262, h2268, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2295_1, u1elo1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2263, hc05, hlam, hphi, ht01, ht0b, ht5b, p2295_1, u1elo2]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [hlam, p2295_0]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2263, hc25, hlam, hphi, ht01, ht0b, ht5b, p2295_1, u1elo2]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2263, hc35, hlam, hphi, ht01, ht0b, ht5b, p2295_1, u1elo2]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2263, h2268, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2295_1, u1elo2]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2261, h2268, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2295_1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2262, hlam, p2295_1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [hlam, p2295_0]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2262, hc35, hlam, hphi, ht01, ht0b, ht5b, p2295_1, u1elo1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2262, h2268, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2295_1, u1elo1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2261, h2268, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2295_1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2263, hlam, p2295_1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2266, hlam, p2295_0]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [hlam, p2295_0]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2268, hlam, p2295_0]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2261, hlam, p2295_1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2264, hlam, p2295_1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2267, hlam, p2295_1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [h2267, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p2295_1]
                · have p2295_0 := h2295c.1
                  have p2295_1 := h2295c.2.1
                  have p2295_2 := h2295c.2.2.1
                  have p2295_3 := h2295c.2.2.2
                  linarith only [hlam, p2295_0]
            · linarith only [h1741, h2261, h2267, hlam]
          · linarith only [h2263, h2265, h2266, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2323 | h2323
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2324 | h2324
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2325 | h2325
              · rcases h5bigk with h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c | h2326c
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [hlam, p2326_0]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h0, hlam, p2326_1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h1741, hlam, p2326_0]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h1741, h2262, hc35, hlam, hphi, ht01, ht0b, ht5b, p2326_1, u1elo1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h1741, h2262, hc45, hlam, hphi, ht01, ht0b, ht5b, p2326_1, u1elo1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2263, hc05, hlam, hphi, ht01, ht0b, ht5b, p2326_1, u1elo2]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [hlam, p2326_0]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2263, hc25, hlam, hphi, ht01, ht0b, ht5b, p2326_1, u1elo2]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2263, h2325, hc45, hlam, hphi, ht01, ht0b, ht5b, p2326_1, u1elo2]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2263, hc45, hlam, hphi, ht01, ht0b, ht5b, p2326_1, u1elo2]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2326_1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2262, hlam, p2326_1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [hlam, p2326_0]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2262, h2325, hc45, hlam, hphi, ht01, ht0b, ht5b, p2326_1, u1elo1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2262, hc45, hlam, hphi, ht01, ht0b, ht5b, p2326_1, u1elo1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2326_1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2263, hlam, p2326_1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2323, hlam, p2326_0]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [hlam, p2326_0]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2265, h2323, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2326_1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2261, hlam, p2326_1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2264, hlam, p2326_1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2324, hlam, p2326_1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [h2325, hlam, p2326_1]
                · have p2326_0 := h2326c.1
                  have p2326_1 := h2326c.2.1
                  have p2326_2 := h2326c.2.2.1
                  have p2326_3 := h2326c.2.2.2
                  linarith only [hlam, p2326_0]
              · linarith only [h2261, h2265, h2323, h2325, hc04, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h1741, h2261, h2265, h2323, h2324, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2354 | h2354
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2355 | h2355
              · rcases h5bigk with h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c | h2356c
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [hlam, p2356_0]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h0, hlam, p2356_1]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h1741, hlam, p2356_0]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h1741, h2323, hlam, p2356_1]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h1741, h2263, h2323, hc45, hlam, hphi, ht01, ht0b, ht5b, p2356_1, u1elo2]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2263, hc05, hlam, hphi, ht01, ht0b, ht5b, p2356_1, u1elo2]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [hlam, p2356_0]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2263, hc25, hlam, hphi, ht01, ht0b, ht5b, p2356_1, u1elo2]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2263, h2323, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2356_1, u1elo2]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2263, hc45, hlam, hphi, ht01, ht0b, ht5b, p2356_1, u1elo2]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2356_1]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2262, hlam, p2356_1]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [hlam, p2356_0]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2323, hlam, p2356_1]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2263, h2323, hc45, hlam, hphi, ht01, ht0b, ht5b, p2356_1, u1elo2]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h0, h2263, hc01, hlam, hphi, p2356_1, u1elo2]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2263, hlam, p2356_1]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h1741, h2263, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2356_1, u1elo2]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [hlam, p2356_0]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2263, hc45, hlam, hphi, ht01, ht0b, ht5b, p2356_1, u1elo2]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2261, hlam, p2356_1]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2264, hlam, p2356_1]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2354, hlam, p2356_1]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [h2355, hlam, p2356_1]
                · have p2356_0 := h2356c.1
                  have p2356_1 := h2356c.2.1
                  have p2356_2 := h2356c.2.2.1
                  have p2356_3 := h2356c.2.2.2
                  linarith only [hlam, p2356_0]
              · linarith only [h1741, h2261, h2262, h2265, h2355, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
            · linarith only [h1741, h2261, h2354, hlam]
      · linarith only [h0, h2261, h2264, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2385 | h2385
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2386 | h2386
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2387 | h2387
          · linarith only [h0, h2262, h2263, h2387, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2389 | h2389
            · linarith only [h2386, h2387, h2389, hlam]
            · linarith only [h1741, h2261, h2389, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2392 | h2392
          · linarith only [h2263, h2386, h2392, hc13, hc34, hlam, hphi]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2394 | h2394
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2395 | h2395
              · rcases h5bigk with h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c | h2396c
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [hlam, p2396_0]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h0, hlam, p2396_1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h1741, hlam, p2396_0]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h0, h2263, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2396_1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p2396_1, u1elo4]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2396_1, u1elo4]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [hlam, p2396_0]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h2262, hc25, hlam, hphi, ht01, ht0b, ht5b, p2396_1, u1elo1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h2263, hlam, p2396_0]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h2262, hc45, hlam, hphi, ht01, ht0b, ht5b, p2396_1, u1elo1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2396_1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h2262, hlam, p2396_1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [hlam, p2396_0]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h2392, hlam, p2396_1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h2262, hc45, hlam, hphi, ht01, ht0b, ht5b, p2396_1, u1elo1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2396_1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2396_1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h2392, hc23, hc35, hlam, hphi, p2396_1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [hlam, p2396_0]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  rcases p2396_3 (m.d 0 5) (by simp) with h2416 | h2416
                  · linarith only [h0, h1741, h2262, h2263, h2416, hc01, hlam, hphi, u1elo1]
                  · linarith only [h2261, h2416, hlam]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h2261, hlam, p2396_1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h2385, hlam, p2396_1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h2394, hlam, p2396_1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [h2395, hlam, p2396_1]
                · have p2396_0 := h2396c.1
                  have p2396_1 := h2396c.2.1
                  have p2396_2 := h2396c.2.2.1
                  have p2396_3 := h2396c.2.2.2
                  linarith only [hlam, p2396_0]
              · linarith only [h1741, h2261, h2262, h2386, h2395, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
            · linarith only [h1741, h2261, h2394, hlam]
      · linarith only [h0, h1741, h2261, h2262, h2385, hc01, hlam, hphi, u1elo1]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h2427 | h2427
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2428 | h2428
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2429 | h2429
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2430 | h2430
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2431 | h2431
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2432 | h2432
              · rcases h5bigk with h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c | h2433c
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [hlam, p2433_0]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h0, hlam, p2433_1]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h1741, hlam, p2433_0]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p2433_1, u1elo4]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p2433_1, u1elo4]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2433_1, u1elo4]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [hlam, p2433_0]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h2262, hlam, p2433_0]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h2427, hc35, hlam, hphi, ht01, ht0b, ht5b, p2433_1, u1elo2]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h2427, hc45, hlam, hphi, ht01, ht0b, ht5b, p2433_1, u1elo2]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2433_1]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2433_1]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [hlam, p2433_0]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  rcases p2433_3 (m.d 0 5) (by simp) with h2447 | h2447
                  · linarith only [h1741, h2447, hlam]
                  · linarith only [h0, h2429, h2431, h2447, hc01, hc23, hlam, hphi, ht12, p2433_1]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  rcases p2433_3 (m.d 0 5) (by simp) with h2450 | h2450
                  · linarith only [h1741, h2450, hlam]
                  · linarith only [h2261, h2450, hlam]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2433_1]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h2427, hlam, p2433_1]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h2430, hlam, p2433_0]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [hlam, p2433_0]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h2427, hc45, hlam, hphi, ht01, ht0b, ht5b, p2433_1, u1elo2]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h2261, hlam, p2433_1]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h2428, hlam, p2433_1]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h2431, hlam, p2433_1]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [h2432, hlam, p2433_1]
                · have p2433_0 := h2433c.1
                  have p2433_1 := h2433c.2.1
                  have p2433_2 := h2433c.2.2.1
                  have p2433_3 := h2433c.2.2.2
                  linarith only [hlam, p2433_0]
              · rcases h5bigk with h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c | h2463c
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [hlam, p2463_0]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h0, hlam, p2463_1]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h1741, hlam, p2463_0]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p2463_1, u1elo4]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2432, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2463_1]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2463_1, u1elo4]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [hlam, p2463_0]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2262, hlam, p2463_0]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2427, hc35, hlam, hphi, ht01, ht0b, ht5b, p2463_1, u1elo2]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2427, h2432, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2463_1, u1elo2]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2261, h2429, h2431, h2432, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2463_1]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h0, h2429, h2431, hc01, hc23, hlam, hphi, ht12, p2463_1]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [hlam, p2463_0]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  rcases p2463_3 (m.d 0 5) (by simp) with h2477 | h2477
                  · linarith only [h1741, h2477, hlam]
                  · linarith only [h2261, h2429, h2431, h2432, h2477, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2463_1]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2429, h2431, h2432, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2463_1]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2261, h2432, hlam, p2463_1]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2427, hlam, p2463_1]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2430, hlam, p2463_0]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [hlam, p2463_0]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2432, hlam, p2463_0]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2261, hlam, p2463_1]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2428, hlam, p2463_1]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h2431, hlam, p2463_1]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [h0, h2261, hc35, hlam, hphi, ht01, ht0b, ht5b, p2463_1, u1elo4]
                · have p2463_0 := h2463c.1
                  have p2463_1 := h2463c.2.1
                  have p2463_2 := h2463c.2.2.1
                  have p2463_3 := h2463c.2.2.2
                  linarith only [hlam, p2463_0]
            · linarith only [h1741, h2261, h2431, hlam]
          · linarith only [h2427, h2429, h2430, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2493 | h2493
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2494 | h2494
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2495 | h2495
              · rcases h5bigk with h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c | h2496c
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [hlam, p2496_0]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h0, hlam, p2496_1]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h1741, hlam, p2496_0]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p2496_1, u1elo4]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p2496_1, u1elo4]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2496_1, u1elo4]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [hlam, p2496_0]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h2262, hlam, p2496_0]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h2427, h2495, hc45, hlam, hphi, ht01, ht0b, ht5b, p2496_1, u1elo2]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h2427, hc45, hlam, hphi, ht01, ht0b, ht5b, p2496_1, u1elo2]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2496_1]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2496_1]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [hlam, p2496_0]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h2429, h2493, h2495, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2496_1]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h2429, h2493, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2496_1]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p2496_1]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h2427, hlam, p2496_1]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h2493, hlam, p2496_0]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [hlam, p2496_0]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h2429, h2493, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2496_1]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h2261, hlam, p2496_1]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h2428, hlam, p2496_1]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h2494, hlam, p2496_1]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [h2495, hlam, p2496_1]
                · have p2496_0 := h2496c.1
                  have p2496_1 := h2496c.2.1
                  have p2496_2 := h2496c.2.2.1
                  have p2496_3 := h2496c.2.2.2
                  linarith only [hlam, p2496_0]
              · linarith only [h2262, h2429, h2493, h2495, hc12, hc45, hlam, hphi, ht23, ht34]
            · linarith only [h0, h2261, h2262, h2429, h2493, h2494, hlam]
          · linarith only [h0, h2262, h2427, h2493, hc01, hlam, hphi, u1elo2]
      · linarith only [h0, h2261, h2428, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2526 | h2526
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2527 | h2527
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2528 | h2528
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2529 | h2529
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2530 | h2530
              · rcases h5bigk with h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [hlam, p2531_0]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h0, hlam, p2531_1]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h1741, hlam, p2531_0]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h0, h2427, hlam, p2531_1]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p2531_1, u1elo4]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2531_1, u1elo4]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [hlam, p2531_0]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h2262, hlam, p2531_0]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h2427, hlam, p2531_0]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h2526, hc45, hlam, hphi, ht01, ht0b, ht5b, p2531_1, u1elo3]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2531_1]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2531_1]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [hlam, p2531_0]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h0, h2427, h2528, hc01, hc23, hlam, hphi, ht12, p2531_1]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  rcases p2531_3 (m.d 0 5) (by simp) with h2546 | h2546
                  · linarith only [h1741, h2546, hlam]
                  · linarith only [h2261, h2546, hlam]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h0, h2530, hc01, hc34, hlam, hphi, ht12, ht23, p2531_1]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h0, h2530, hc01, hc34, hlam, hphi, ht12, ht23, p2531_1]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h2528, hlam, p2531_0]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [hlam, p2531_0]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h2527, h2530, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2531_1]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h2261, hlam, p2531_1]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h2526, hlam, p2531_1]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h2529, hlam, p2531_1]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [h2530, hlam, p2531_1]
                · have p2531_0 := h2531c.1
                  have p2531_1 := h2531c.2.1
                  have p2531_2 := h2531c.2.2.1
                  have p2531_3 := h2531c.2.2.2
                  linarith only [hlam, p2531_0]
              · linarith only [h0, h2261, h2427, h2530, hlam]
            · linarith only [h1741, h2261, h2529, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2561 | h2561
            · linarith only [h2527, h2528, h2561, hlam]
            · linarith only [h0, h2261, h2262, h2561, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2564 | h2564
          · linarith only [h2427, h2527, h2564, hc13, hc34, hlam, hphi]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2566 | h2566
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2567 | h2567
              · rcases h5bigk with h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c | h2568c
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [hlam, p2568_0]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h0, hlam, p2568_1]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h1741, hlam, p2568_0]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h2564, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2568_1]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p2568_1, u1elo4]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p2568_1, u1elo4]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [hlam, p2568_0]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h2262, hlam, p2568_0]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h2427, hlam, p2568_0]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p2568_1, u1elo4]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2568_1]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2568_1]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [hlam, p2568_0]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h2564, hlam, p2568_1]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  rcases p2568_3 (m.d 0 5) (by simp) with h2583 | h2583
                  · linarith only [h1741, h2583, hlam]
                  · linarith only [h2261, h2583, hlam]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h0, h2567, hc01, hc34, hlam, hphi, ht12, ht23, p2568_1]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h0, h2567, hc01, hc34, hlam, hphi, ht12, ht23, p2568_1]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h1741, h2567, hc02, hc34, hlam, hphi, ht23, p2568_1]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [hlam, p2568_0]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  rcases p2568_3 (m.d 0 5) (by simp) with h2590 | h2590
                  · linarith only [h0, h2427, h2590, hlam]
                  · linarith only [h2261, h2590, hlam]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h2261, hlam, p2568_1]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h2526, hlam, p2568_1]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h2566, hlam, p2568_1]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [h2567, hlam, p2568_1]
                · have p2568_0 := h2568c.1
                  have p2568_1 := h2568c.2.1
                  have p2568_2 := h2568c.2.2.1
                  have p2568_3 := h2568c.2.2.2
                  linarith only [hlam, p2568_0]
              · linarith only [h2526, h2527, h2567, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
            · linarith only [h0, h2261, h2262, h2566, hlam]
      · linarith only [h0, h2261, h2526, hlam]

end R2N4
