import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_I_L_0_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have hc13 := m.hcor 1 3 (by decide)
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
              · rcases h5bigk with h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [hlam, p8_0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h0, hlam, p8_0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [hlam, p8_0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h0, h6, hc35, hlam, hphi, ht0b, ht5b, p8_1, u0elo0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p8_1, u0elo0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p8_1, u0elo0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h1, hlam, p8_1]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p8_1, u0elo1]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [hlam, p8_0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h1, hc35, hlam, hphi, ht0b, ht5b, p8_1, u0elo1]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p8_1, u0elo1]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h2, hlam, p8_0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h4, hlam, p8_0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h6, hlam, p8_0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [hlam, p8_0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo4]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h3, hlam, p8_0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h3, hc15, hlam, hphi, ht0b, ht5b, p8_1, u0elo3]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h7, hlam, p8_0]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8_1, u3elo2]
                · have p8_0 := h8c.1
                  have p8_1 := h8c.2.1
                  have p8_2 := h8c.2.2.1
                  have p8_3 := h8c.2.2.2
                  linarith only [hlam, p8_0]
              · rcases h5bigk with h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c | h34c
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [hlam, p34_0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h2, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p34_1, u3elo0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p34_1, u3elo0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p34_1, u3elo0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h2, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p34_1, u3elo0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h0, hlam, p34_0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [hlam, p34_0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h0, h5, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, p34_1, u0elo0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p34_1, u0elo0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h0, h5, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, p34_1, u0elo0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h1, hlam, p34_1]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p34_1, u0elo1]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [hlam, p34_0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h1, hc35, hlam, hphi, ht0b, ht5b, p34_1, u0elo1]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h7, hlam, p34_1]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h2, hlam, p34_0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h4, hlam, p34_0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h6, hlam, p34_0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [hlam, p34_0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p34_1, u3elo4]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h3, hlam, p34_0]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h3, hc15, hlam, hphi, ht0b, ht5b, p34_1, u0elo3]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h3, h5, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, p34_1, u0elo3]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [h3, hc35, hlam, hphi, ht0b, ht5b, p34_1, u0elo3]
                · have p34_0 := h34c.1
                  have p34_1 := h34c.2.1
                  have p34_2 := h34c.2.2.1
                  have p34_3 := h34c.2.2.2
                  linarith only [hlam, p34_0]
            · linarith only [h2, h6, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
            · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
              · rcases h5bigk with h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, h61, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, h61, hc35, hlam, hphi, ht0b, ht5b, p63_1, u0elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p63_1, u0elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p63_1, u0elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h1, hlam, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p63_1, u0elo1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h1, hc35, hlam, hphi, ht0b, ht5b, p63_1, u0elo1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h5, h61, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h4, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h61, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo4]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h3, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h3, hc15, hlam, hphi, ht0b, ht5b, p63_1, u0elo3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h62, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h5, h61, h62, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
              · linarith only [h3, h5, h61, h62, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
            · linarith only [h2, h61, hc23, hlam, hphi, u3elo0]
        · linarith only [h2, h4, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
        · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
          · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
            · rcases m.htr 2 4 5 (by decide) (by decide) with h95 | h95
              · linarith only [h1, h3, h95, hlam]
              · rcases h5bigk with h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [hlam, p97_0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p97_1, u0elo4]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h0, hc25, hlam, hphi, ht0b, ht5b, p97_1, u0elo0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p97_1, u3elo0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h3, hlam, p97_1]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h0, hlam, p97_0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [hlam, p97_0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h0, h93, h95, hc34, hlam, hphi, ht0b, ht45, ht5b, p97_1, u0elo0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p97_1, u0elo0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h0, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, p97_1, u0elo0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h1, hlam, p97_1]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p97_1, u0elo1]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [hlam, p97_0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h1, hc35, hlam, hphi, ht0b, ht5b, p97_1, u0elo4]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h95, hlam, p97_1]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h2, hlam, p97_0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h92, hlam, p97_0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h94, hlam, p97_0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [hlam, p97_0]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h3, h92, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p97_1]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h3, hc04, hc45, hlam, hphi, p97_1]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  rcases p97_3 (m.d 0 5) (by simp) with h119 | h119
                  · linarith only [h119, h3, hlam]
                  · linarith only [h0, h119, hlam]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [h93, h95, hc34, hc45, hlam, hphi, p97_1]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  rcases p97_3 (m.d 0 5) (by simp) with h123 | h123
                  · linarith only [h123, h3, hlam]
                  · linarith only [h123, h2, hlam]
                · have p97_0 := h97c.1
                  have p97_1 := h97c.2.1
                  have p97_2 := h97c.2.2.1
                  have p97_3 := h97c.2.2.2
                  linarith only [hlam, p97_0]
            · linarith only [h2, h94, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h128 | h128
            · rcases m.htr 2 4 5 (by decide) (by decide) with h129 | h129
              · linarith only [h1, h129, h3, hlam]
              · linarith only [h128, h129, h93, hlam]
            · linarith only [h128, h2, hc23, hlam, hphi, u3elo0]
        · linarith only [h2, h92, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
      · rcases m.htr 1 3 5 (by decide) (by decide) with h135 | h135
        · linarith only [h135, h2, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
          · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
            · linarith only [h135, h138, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h140 | h140
              · linarith only [h137, h138, h140, hlam]
              · rcases h5bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p142_1, u0elo4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h0, h138, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p142_1, u0elo0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h2, hlam, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h140, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p142_1, u3elo4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h0, hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h137, h138, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h135, hlam, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h0, h137, h138, h140, hc34, hlam, hphi, ht0b, ht45, ht5b, p142_1, u0elo0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h1, hlam, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p142_1, u0elo1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h138, hlam, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h140, hlam, p142_1]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p142_1, u3elo4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p142_1, u3elo4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p142_1, u3elo4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h138, h140, hc23, hlam, hphi, p142_1, u3elo4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h134, hlam, p142_0]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h134, h135, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p142_1, u0elo4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h134, h137, h138, hc34, hlam, hphi, ht0b, ht45, ht5b, p142_1, u0elo4]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [h134, h2, hc05, hlam, hphi, ht0b, ht5b, p142_1, u0elo3]
                · have p142_0 := h142c.1
                  have p142_1 := h142c.2.1
                  have p142_2 := h142c.2.2.1
                  have p142_3 := h142c.2.2.2
                  linarith only [hlam, p142_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h168 | h168
            · linarith only [h137, h168, h2, hc03, hlam, hphi, u3elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h170 | h170
              · rcases h5bigk with h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [hlam, p171_0]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h135, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p171_1, u0elo4]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h168, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p171_1, u0elo4]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h2, hlam, p171_1]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p171_1, u3elo4]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h0, hlam, p171_0]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [hlam, p171_0]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h0, h168, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p171_1, u0elo0]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h135, hlam, p171_1]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p171_1, u0elo0]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h1, hlam, p171_1]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p171_1, u0elo1]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [hlam, p171_0]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h168, hlam, p171_1]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p171_1, u0elo1]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p171_1, u3elo4]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h135, hc13, hlam, hphi, p171_1, u3elo4]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p171_1, u3elo4]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [hlam, p171_0]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p171_1, u3elo4]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h134, hlam, p171_0]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h135, h170, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p171_1]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h170, hlam, p171_0]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [h1, h170, hc35, hlam, hphi, ht0b, ht5b, p171_1, u0elo1]
                · have p171_0 := h171c.1
                  have p171_1 := h171c.2.1
                  have p171_2 := h171c.2.2.1
                  have p171_3 := h171c.2.2.2
                  linarith only [hlam, p171_0]
              · rcases h5bigk with h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [hlam, p197_0]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h135, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1, u0elo4]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p197_1, u3elo4]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h2, hlam, p197_1]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h137, h170, h2, hc23, hlam, hphi, p197_1, u3elo4]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h0, hlam, p197_0]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [hlam, p197_0]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h0, h137, h170, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1, u0elo0]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h135, hlam, p197_1]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h0, h137, h170, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1, u0elo0]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h1, hlam, p197_1]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p197_1, u0elo1]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [hlam, p197_0]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h168, hlam, p197_1]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h170, hlam, p197_1]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p197_1, u3elo4]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p197_1, u3elo4]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p197_1, u3elo4]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [hlam, p197_0]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h137, h170, hc23, hlam, hphi, p197_1, u3elo4]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h134, hlam, p197_0]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h134, h135, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1, u0elo4]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h134, h137, h170, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1, u0elo3]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [h134, h2, hc05, hlam, hphi, ht0b, ht5b, p197_1, u0elo3]
                · have p197_0 := h197c.1
                  have p197_1 := h197c.2.1
                  have p197_2 := h197c.2.2.1
                  have p197_3 := h197c.2.2.2
                  linarith only [hlam, p197_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h223 | h223
        · linarith only [h2, h223, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
          · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
            · linarith only [h2, h226, hc03, hlam, hphi, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h228 | h228
              · linarith only [h1, h134, h225, h226, h228, hlam]
              · rcases h5bigk with h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c | h230c
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [hlam, p230_0]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h223, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p230_1, u0elo4]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h0, h225, h226, hc34, hlam, hphi, ht0b, ht45, ht5b, p230_1, u0elo0]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h2, hlam, p230_1]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h134, hlam, p230_1]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h0, hlam, p230_0]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [hlam, p230_0]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h225, h226, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p230_1]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h223, hlam, p230_1]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h0, h134, hc05, hlam, hphi, ht0b, ht5b, p230_1, u0elo0]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h1, hlam, p230_1]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h1, h223, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p230_1, u0elo4]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [hlam, p230_0]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h226, hlam, p230_1]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h228, hlam, p230_1]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p230_1, u3elo4]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h223, hc13, hlam, hphi, p230_1, u3elo4]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p230_1, u3elo4]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [hlam, p230_0]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h228, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p230_1, u3elo4]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h1, h225, h226, hc34, hc45, hlam, hphi, p230_1]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h223, hc13, hc45, hlam, hphi, ht34, p230_1]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h225, h226, hc34, hc45, hlam, hphi, p230_1]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [h2, hc03, hc45, hlam, hphi, ht34, p230_1]
                · have p230_0 := h230c.1
                  have p230_1 := h230c.2.1
                  have p230_2 := h230c.2.2.1
                  have p230_3 := h230c.2.2.2
                  linarith only [hlam, p230_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h256 | h256
            · linarith only [h0, h2, h223, h225, h256, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h258 | h258
              · linarith only [h1, h134, h258, hlam]
              · rcases h5bigk with h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [hlam, p260_0]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h223, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p260_1, u0elo4]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h2, h258, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p260_1, u3elo4]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h2, hlam, p260_1]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h134, hlam, p260_1]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h0, hlam, p260_0]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [hlam, p260_0]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h0, h225, h258, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p260_1, u0elo0]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h223, hlam, p260_1]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h0, h134, hc05, hlam, hphi, ht0b, ht5b, p260_1, u0elo0]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h1, hlam, p260_1]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h1, h223, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p260_1, u0elo4]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [hlam, p260_0]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h256, hlam, p260_1]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h258, hlam, p260_1]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p260_1, u3elo4]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h223, hc13, hlam, hphi, p260_1, u3elo4]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p260_1, u3elo4]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [hlam, p260_0]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h225, h258, hc23, hlam, hphi, p260_1, u3elo4]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h1, h225, h258, hc23, hc45, hlam, hphi, ht34, p260_1]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h223, hc13, hc45, hlam, hphi, ht34, p260_1]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h225, h258, hc23, hc45, hlam, hphi, ht34, p260_1]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [h2, hc03, hc45, hlam, hphi, ht34, p260_1]
                · have p260_0 := h260c.1
                  have p260_1 := h260c.2.1
                  have p260_2 := h260c.2.2.1
                  have p260_3 := h260c.2.2.2
                  linarith only [hlam, p260_0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h286 | h286
    · rcases m.htr 0 4 5 (by decide) (by decide) with h287 | h287
      · rcases m.htr 1 3 5 (by decide) (by decide) with h288 | h288
        · rcases m.htr 2 3 4 (by decide) (by decide) with h289 | h289
          · rcases m.htr 2 3 5 (by decide) (by decide) with h290 | h290
            · rcases m.htr 2 4 5 (by decide) (by decide) with h291 | h291
              · rcases h5bigk with h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p292_1, u0elo4]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h1, hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h286, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p292_1, u3elo0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h286, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p292_1, u3elo0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h0, hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h0, h1, hc05, hlam, hphi, ht0b, ht5b, p292_1, u0elo0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p292_1, u0elo4]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p292_1, u0elo0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h289, h291, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p292_1, u3elo2]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h289, h291, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p292_1, u3elo2]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h289, h291, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p292_1, u3elo2]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h289, h291, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p292_1, u3elo2]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h286, hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h288, hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h290, hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h288, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p292_1]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h287, hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h287, hc15, hlam, hphi, ht0b, ht5b, p292_1, u0elo3]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h291, hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h287, hc35, hlam, hphi, ht0b, ht5b, p292_1, u0elo4]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [hlam, p292_0]
              · linarith only [h1, h287, h291, hlam]
            · linarith only [h286, h290, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h320 | h320
            · linarith only [h1, h289, h320, hc02, hlam, hphi, ht23, u3elo3]
            · linarith only [h286, h320, hc23, hlam, hphi, u3elo0]
        · linarith only [h286, h288, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h324 | h324
        · rcases m.htr 2 3 4 (by decide) (by decide) with h325 | h325
          · rcases m.htr 2 3 5 (by decide) (by decide) with h326 | h326
            · rcases m.htr 2 4 5 (by decide) (by decide) with h327 | h327
              · rcases h5bigk with h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c | h328c
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h287, h325, h327, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p328_1, u3elo2]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h1, hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h287, h325, h327, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p328_1, u3elo2]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h287, hlam, p328_1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h0, hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h1, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p328_1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h0, h287, h325, h327, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p328_1, u3elo2]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h0, h287, hlam, p328_1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h1, hc02, hc25, hlam, hphi, p328_1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h325, h327, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p328_1, u3elo2]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h325, h327, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p328_1, u3elo2]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h287, h325, h327, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p328_1, u3elo2]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h286, hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h324, hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h326, hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h287, h324, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p328_1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p328_1]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h325, h327, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p328_1, u3elo2]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h327, hlam, p328_0]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [h325, h327, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p328_1, u3elo2]
                · have p328_0 := h328c.1
                  have p328_1 := h328c.2.1
                  have p328_2 := h328c.2.2.1
                  have p328_3 := h328c.2.2.2
                  linarith only [hlam, p328_0]
              · rcases h5bigk with h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c | h354c
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [hlam, p354_0]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h324, hc35, hlam, hphi, ht0b, ht5b, p354_1, u0elo4]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h1, hlam, p354_0]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [hc35, hlam, hphi, ht0b, ht5b, p354_1, u0elo4]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h287, hlam, p354_1]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h0, hlam, p354_0]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [hlam, p354_0]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h0, h1, hc05, hlam, hphi, ht0b, ht5b, p354_1, u0elo0]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p354_1, u0elo0]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h0, h1, h327, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p354_1, u0elo4]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h1, h327, hc02, hc45, hlam, hphi, ht23, ht34, p354_1]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h326, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p354_1, u3elo2]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [hlam, p354_0]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h326, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p354_1, u3elo2]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h327, hlam, p354_1]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h286, hlam, p354_0]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h324, hlam, p354_0]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h326, hlam, p354_0]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [hlam, p354_0]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p354_1, u3elo4]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p354_1]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  rcases p354_3 (m.d 0 5) (by simp) with h376 | h376
                  · linarith only [h287, h376, hlam]
                  · linarith only [h0, h376, hlam]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p354_1]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  rcases p354_3 (m.d 0 5) (by simp) with h380 | h380
                  · linarith only [h287, h380, hlam]
                  · linarith only [h286, h380, hlam]
                · have p354_0 := h354c.1
                  have p354_1 := h354c.2.1
                  have p354_2 := h354c.2.2.1
                  have p354_3 := h354c.2.2.2
                  linarith only [hlam, p354_0]
            · linarith only [h286, h326, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h385 | h385
            · linarith only [h1, h325, h385, hc02, hlam, hphi, ht23, u3elo3]
            · linarith only [h286, h385, hc23, hlam, hphi, u3elo0]
        · linarith only [h286, h324, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h389 | h389
      · rcases m.htr 1 3 5 (by decide) (by decide) with h390 | h390
        · linarith only [h286, h390, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h392 | h392
          · rcases m.htr 2 3 5 (by decide) (by decide) with h393 | h393
            · linarith only [h390, h393, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h395 | h395
              · linarith only [h1, h392, h393, h395, hc02, hlam, hphi, ht23, u3elo4]
              · linarith only [h1, h389, h395, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h398 | h398
            · linarith only [h286, h392, h398, hc03, hlam, hphi, u3elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h400 | h400
              · rcases h5bigk with h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c | h401c
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [hlam, p401_0]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p401_1, u0elo4]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h1, hlam, p401_0]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h286, hlam, p401_1]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h286, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p401_1, u3elo4]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h0, hlam, p401_0]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [hlam, p401_0]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h0, h1, hc05, hlam, hphi, ht0b, ht5b, p401_1, u0elo0]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h390, hlam, p401_1]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p401_1, u0elo0]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h1, hc02, hc25, hlam, hphi, p401_1]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h392, h400, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p401_1, u3elo3]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [hlam, p401_0]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h398, hlam, p401_1]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h392, h400, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p401_1, u3elo3]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p401_1, u3elo4]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h390, hc13, hlam, hphi, p401_1, u3elo4]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p401_1, u3elo4]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [hlam, p401_0]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p401_1, u3elo4]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h389, hlam, p401_0]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h390, hc13, hc45, hlam, hphi, ht34, p401_1]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h400, hlam, p401_0]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [h389, hc35, hlam, hphi, ht0b, ht5b, p401_1, u0elo4]
                · have p401_0 := h401c.1
                  have p401_1 := h401c.2.1
                  have p401_2 := h401c.2.2.1
                  have p401_3 := h401c.2.2.2
                  linarith only [hlam, p401_0]
              · linarith only [h1, h389, h400, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h428 | h428
        · linarith only [h286, h428, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
          · rcases m.htr 2 3 5 (by decide) (by decide) with h431 | h431
            · linarith only [h286, h431, hc03, hlam, hphi, u3elo2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h433 | h433
              · linarith only [h389, h430, h431, h433, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
              · rcases h5bigk with h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c | h435c
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [hlam, p435_0]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h428, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p435_1, u0elo4]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h1, hlam, p435_0]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h286, hlam, p435_1]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h389, hlam, p435_1]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h0, hlam, p435_0]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [hlam, p435_0]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h1, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p435_1]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h428, hlam, p435_1]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h0, h1, h433, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p435_1, u0elo4]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h1, hc02, hc25, hlam, hphi, p435_1]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h428, h431, hc13, hlam, hphi, p435_1, u3elo4]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [hlam, p435_0]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h431, hlam, p435_1]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h433, hlam, p435_1]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht23, p435_1, u3elo4]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h428, hc13, hlam, hphi, p435_1, u3elo4]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p435_1, u3elo4]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [hlam, p435_0]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p435_1, u3elo4]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p435_1]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h428, hc13, hc45, hlam, hphi, ht34, p435_1]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p435_1]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [h431, hc23, hc45, hlam, hphi, ht34, p435_1]
                · have p435_0 := h435c.1
                  have p435_1 := h435c.2.1
                  have p435_2 := h435c.2.2.1
                  have p435_3 := h435c.2.2.2
                  linarith only [hlam, p435_0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h461 | h461
            · linarith only [h286, h430, h461, hc03, hlam, hphi, u3elo3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h463 | h463
              · rcases h5bigk with h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c | h464c
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [hlam, p464_0]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h428, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p464_1, u0elo4]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h1, hlam, p464_0]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h286, hlam, p464_1]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h389, hlam, p464_1]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h0, hlam, p464_0]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [hlam, p464_0]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h1, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p464_1]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h428, hlam, p464_1]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h0, h389, hlam, p464_1]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h1, hc02, hc25, hlam, hphi, p464_1]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h430, h463, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p464_1, u3elo3]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [hlam, p464_0]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h461, hlam, p464_1]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h389, h430, h463, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p464_1, u3elo3]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht23, p464_1, u3elo4]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h428, hc13, hlam, hphi, p464_1, u3elo4]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p464_1, u3elo4]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [hlam, p464_0]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h389, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p464_1, u3elo4]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p464_1]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h428, h430, h463, hc13, hlam, hphi, p464_1, u3elo3]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h463, hlam, p464_0]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [h430, h463, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p464_1, u3elo3]
                · have p464_0 := h464c.1
                  have p464_1 := h464c.2.1
                  have p464_2 := h464c.2.2.1
                  have p464_3 := h464c.2.2.2
                  linarith only [hlam, p464_0]
              · rcases h5bigk with h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [hlam, p490_0]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h428, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p490_1, u0elo4]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h1, hlam, p490_0]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h286, hlam, p490_1]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h389, hlam, p490_1]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h0, hlam, p490_0]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [hlam, p490_0]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h1, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p490_1]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h428, hlam, p490_1]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h0, h1, h463, hlam, p490_1]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h0, h461, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p490_1, u3elo4]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h428, h461, hc13, hlam, hphi, p490_1, u3elo4]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [hlam, p490_0]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h461, hlam, p490_1]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h463, hlam, p490_1]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h1, hc02, hlam, hphi, ht23, p490_1, u3elo4]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h428, hc13, hlam, hphi, p490_1, u3elo4]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p490_1, u3elo4]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [hlam, p490_0]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h1, h463, hc02, hlam, hphi, ht23, p490_1, u3elo4]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p490_1]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h428, hc13, hc45, hlam, hphi, ht34, p490_1]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p490_1]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [h286, hc03, hc45, hlam, hphi, ht34, p490_1]
                · have p490_0 := h490c.1
                  have p490_1 := h490c.2.1
                  have p490_2 := h490c.2.2.1
                  have p490_3 := h490c.2.2.2
                  linarith only [hlam, p490_0]

end R2N4
