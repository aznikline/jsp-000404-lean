import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_0_M_LI_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
        · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
              · rcases h5bigk with h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [hlam, p9_0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [hc15, hlam, hphi, p9_1, u5elo0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [hc25, hlam, hphi, p9_1, u5elo0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [hc35, hlam, hphi, p9_1, u5elo0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [hc45, hlam, hphi, p9_1, u5elo0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h0, hlam, p9_0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [hlam, p9_0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [hc25, hlam, hphi, p9_1, u5elo1]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h0, h8, hc45, hlam, hphi, ht0b, ht5b, p9_1, u0elo0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht0b, ht5b, p9_1, u0elo0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h1, hlam, p9_1]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h4, hlam, p9_1]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [hlam, p9_0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h8, hc45, hlam, hphi, p9_1, u5elo2]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9_1, u2elo0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h2, hlam, p9_0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [hc15, hlam, hphi, p9_1, u5elo3]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h6, hlam, p9_0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [hlam, p9_0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [hc45, hlam, hphi, p9_1, u5elo3]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h3, hlam, p9_0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h5, hlam, p9_0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h7, hlam, p9_0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [h8, hlam, p9_0]
                · have p9_0 := h9c.1
                  have p9_1 := h9c.2.1
                  have p9_2 := h9c.2.2.1
                  have p9_3 := h9c.2.2.2
                  linarith only [hlam, p9_0]
              · rcases h5bigk with h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [hlam, p35_0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [hc15, hlam, hphi, p35_1, u5elo0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [hc25, hlam, hphi, p35_1, u5elo0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [hc35, hlam, hphi, p35_1, u5elo0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h8, hc34, hlam, hphi, ht45, p35_1, u5elo0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h0, hlam, p35_0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [hlam, p35_0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [hc25, hlam, hphi, p35_1, u5elo1]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h0, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, p35_1, u0elo0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h0, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, p35_1, u0elo0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h1, hlam, p35_1]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h4, hlam, p35_1]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [hlam, p35_0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h8, hc34, hlam, hphi, ht45, p35_1, u5elo2]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h1, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p35_1, u2elo0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h2, hlam, p35_0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [hc15, hlam, hphi, p35_1, u5elo3]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h6, hlam, p35_0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [hlam, p35_0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h8, hlam, p35_1]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h3, hlam, p35_0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h5, hlam, p35_0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [h7, hlam, p35_0]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [hc35, hlam, hphi, p35_1, u5elo4]
                · have p35_0 := h35c.1
                  have p35_1 := h35c.2.1
                  have p35_2 := h35c.2.2.1
                  have p35_3 := h35c.2.2.2
                  linarith only [hlam, p35_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h61 | h61
              · linarith only [h6, h61, h7, hlam]
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
                  linarith only [hc15, hlam, hphi, p63_1, u5elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hc25, hlam, hphi, p63_1, u5elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hc35, hlam, hphi, p63_1, u5elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h7, hc24, hlam, hphi, ht45, p63_1, u5elo0]
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
                  linarith only [h6, hc35, hlam, hphi, p63_1, u5elo1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, h61, hc34, hlam, hphi, ht0b, ht45, ht5b, p63_1, u0elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, p63_1, u0elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h1, hlam, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h4, hlam, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h61, hc34, hlam, hphi, ht45, p63_1, u5elo2]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h7, hlam, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hc15, hlam, hphi, p63_1, u5elo3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h6, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h61, hlam, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h3, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h5, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hc25, hlam, hphi, p63_1, u5elo4]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, h5, hc35, hlam, hphi, ht0b, ht5b, p63_1, u0elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
          · linarith only [h2, h6, hc23, hlam, hphi, u3elo0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
          · rcases m.htr 2 4 5 (by decide) (by decide) with h91 | h91
            · linarith only [h4, h5, h91, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h93 | h93
              · linarith only [h4, h5, h90, h93, hlam]
              · rcases h5bigk with h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c | h95c
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [hlam, p95_0]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [hc15, hlam, hphi, p95_1, u5elo0]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h90, hc35, hlam, hphi, p95_1, u5elo0]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [hc35, hlam, hphi, p95_1, u5elo0]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h5, hc14, hlam, hphi, ht45, p95_1, u5elo0]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h0, hlam, p95_0]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [hlam, p95_0]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h90, hc35, hlam, hphi, p95_1, u5elo1]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h93, hc34, hlam, hphi, ht45, p95_1, u5elo1]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h5, hlam, p95_1]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h1, hlam, p95_1]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h4, hlam, p95_1]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [hlam, p95_0]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h93, hc34, hlam, hphi, ht45, p95_1, u5elo2]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h91, hlam, p95_1]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h2, hlam, p95_0]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [hc15, hlam, hphi, p95_1, u5elo3]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h90, hlam, p95_0]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [hlam, p95_0]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h93, hlam, p95_1]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h3, hlam, p95_0]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h3, hc15, hlam, hphi, ht0b, ht5b, p95_1, u0elo3]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h3, h90, hc35, hlam, hphi, ht0b, ht5b, p95_1, u0elo3]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [h3, hc35, hlam, hphi, ht0b, ht5b, p95_1, u0elo3]
                · have p95_0 := h95c.1
                  have p95_1 := h95c.2.1
                  have p95_2 := h95c.2.2.1
                  have p95_3 := h95c.2.2.2
                  linarith only [hlam, p95_0]
          · linarith only [h2, h90, hc23, hlam, hphi, u3elo0]
      · linarith only [h1, h4, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h123 | h123
      · rcases m.htr 1 4 5 (by decide) (by decide) with h124 | h124
        · linarith only [h0, h124, h3, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
          · rcases m.htr 2 4 5 (by decide) (by decide) with h127 | h127
            · linarith only [h0, h123, h127, h3, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h129 | h129
              · linarith only [h0, h123, h126, h129, h3, hlam]
              · rcases h5bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [hlam, p131_0]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [hc15, hlam, hphi, p131_1, u5elo0]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h126, h3, hc35, hlam, hphi, p131_1, u5elo4]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h3, hc35, hlam, hphi, p131_1, u5elo4]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h3, hlam, p131_1]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h0, hlam, p131_0]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [hlam, p131_0]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h126, hc35, hlam, hphi, p131_1, u5elo1]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h0, h129, h3, hc34, hlam, hphi, ht45, p131_1, u5elo4]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h124, hlam, p131_1]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h1, hlam, p131_1]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h123, hlam, p131_1]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [hlam, p131_0]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h129, hc34, hlam, hphi, ht45, p131_1, u5elo2]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h127, hlam, p131_1]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h2, hlam, p131_0]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [hc15, hlam, hphi, p131_1, u5elo3]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h126, hlam, p131_0]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [hlam, p131_0]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h129, hlam, p131_1]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [hc05, hlam, hphi, p131_1, u5elo4]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [hc15, hlam, hphi, p131_1, u5elo4]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [h126, hc35, hlam, hphi, p131_1, u5elo4]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [hc35, hlam, hphi, p131_1, u5elo4]
                · have p131_0 := h131c.1
                  have p131_1 := h131c.2.1
                  have p131_2 := h131c.2.2.1
                  have p131_3 := h131c.2.2.2
                  linarith only [hlam, p131_0]
          · linarith only [h126, h2, hc23, hlam, hphi, u3elo0]
      · linarith only [h1, h123, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h159 | h159
    · rcases m.htr 1 2 5 (by decide) (by decide) with h160 | h160
      · rcases m.htr 1 4 5 (by decide) (by decide) with h161 | h161
        · rcases m.htr 2 3 5 (by decide) (by decide) with h162 | h162
          · linarith only [h162, h2, hc03, hlam, hphi, u3elo2]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h164 | h164
            · rcases m.htr 3 4 5 (by decide) (by decide) with h165 | h165
              · rcases h5bigk with h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [hlam, p166_0]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h160, h162, hc23, hlam, hphi, ht34, ht45, p166_1, u5elo0]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h162, hc23, hlam, hphi, ht34, ht45, p166_1, u5elo0]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h2, hlam, p166_1]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [hc45, hlam, hphi, p166_1, u5elo0]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h0, hlam, p166_0]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [hlam, p166_0]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h162, hc23, hlam, hphi, ht34, ht45, p166_1, u5elo1]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h0, h2, hlam, p166_1]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h0, h2, hc45, hlam, hphi, p166_1, u5elo3]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h1, hlam, p166_1]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h160, hlam, p166_1]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [hlam, p166_0]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h162, hlam, p166_1]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [hc45, hlam, hphi, p166_1, u5elo2]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [hc05, hlam, hphi, p166_1, u5elo3]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [hc15, hlam, hphi, p166_1, u5elo3]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [hc25, hlam, hphi, p166_1, u5elo3]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [hlam, p166_0]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [hc45, hlam, hphi, p166_1, u5elo3]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h159, hlam, p166_0]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h161, hlam, p166_0]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h164, hlam, p166_0]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [h165, hlam, p166_0]
                · have p166_0 := h166c.1
                  have p166_1 := h166c.2.1
                  have p166_2 := h166c.2.2.1
                  have p166_3 := h166c.2.2.2
                  linarith only [hlam, p166_0]
              · linarith only [h0, h160, h164, h165, h2, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h193 | h193
              · rcases h5bigk with h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hc15, hlam, hphi, p194_1, u5elo0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hc25, hlam, hphi, p194_1, u5elo0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h2, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h164, h2, hc24, hlam, hphi, ht45, p194_1, u5elo3]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h0, hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hc25, hlam, hphi, p194_1, u5elo1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h0, h2, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h0, h164, h2, hc24, hlam, hphi, ht45, p194_1, u5elo3]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h1, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h160, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h162, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h164, hlam, p194_1]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hc05, hlam, hphi, p194_1, u5elo3]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h161, h164, hc24, hlam, hphi, ht45, p194_1, u5elo3]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h162, hc23, hlam, hphi, ht34, ht45, p194_1, u5elo3]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h164, hc24, hlam, hphi, ht45, p194_1, u5elo3]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h159, hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h161, hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h162, h193, hc23, hlam, hphi, p194_1, u3elo3]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [h193, hlam, p194_0]
                · have p194_0 := h194c.1
                  have p194_1 := h194c.2.1
                  have p194_2 := h194c.2.2.1
                  have p194_3 := h194c.2.2.2
                  linarith only [hlam, p194_0]
              · linarith only [h0, h161, h193, h2, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h221 | h221
          · linarith only [h2, h221, hc03, hlam, hphi, u3elo2]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h223 | h223
            · linarith only [h160, h161, h223, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h225 | h225
              · rcases h5bigk with h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c | h226c
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [hlam, p226_0]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h160, hc25, hlam, hphi, p226_1, u5elo0]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [hc25, hlam, hphi, p226_1, u5elo0]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h2, hlam, p226_1]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h161, h2, hc14, hlam, hphi, ht45, p226_1, u5elo3]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h0, hlam, p226_0]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [hlam, p226_0]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [hc25, hlam, hphi, p226_1, u5elo1]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h2, hc05, hlam, hphi, p226_1, u5elo1]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h161, hlam, p226_1]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h1, hlam, p226_1]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h160, hlam, p226_1]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [hlam, p226_0]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h221, hlam, p226_1]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h223, hlam, p226_1]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h159, h223, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p226_1, u3elo4]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h160, h221, hc23, hlam, hphi, ht34, ht45, p226_1, u5elo3]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h221, hc23, hlam, hphi, ht34, ht45, p226_1, u5elo3]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [hlam, p226_0]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h223, hc24, hlam, hphi, ht45, p226_1, u5elo3]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h159, hlam, p226_0]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h159, h160, h221, hc23, hlam, hphi, ht34, ht45, p226_1, u5elo0]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h159, h2, h221, hc23, hlam, hphi, ht34, ht45, p226_1, u5elo3]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [h225, hlam, p226_0]
                · have p226_0 := h226c.1
                  have p226_1 := h226c.2.1
                  have p226_2 := h226c.2.2.1
                  have p226_3 := h226c.2.2.2
                  linarith only [hlam, p226_0]
              · linarith only [h159, h2, h225, hlam]
      · linarith only [h1, h160, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
      · rcases m.htr 1 4 5 (by decide) (by decide) with h255 | h255
        · linarith only [h0, h159, h255, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h257 | h257
          · linarith only [h2, h257, hc03, hlam, hphi, u3elo2]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h259 | h259
            · linarith only [h0, h159, h254, h259, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h261 | h261
              · rcases h5bigk with h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c | h262c
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h159, h261, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p262_1, u3elo3]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h159, h261, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p262_1, u3elo3]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h2, hlam, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h159, hlam, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h0, hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [hc25, hlam, hphi, p262_1, u5elo1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h0, h159, h261, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p262_1, u3elo3]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h255, hlam, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h1, hlam, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h254, hlam, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h257, hlam, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h259, hlam, p262_1]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [hc05, hlam, hphi, p262_1, u5elo3]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h254, h257, hc23, hlam, hphi, ht34, ht45, p262_1, u5elo3]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h257, hc23, hlam, hphi, ht34, ht45, p262_1, u5elo3]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h159, hc04, hlam, hphi, ht45, p262_1, u5elo3]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h0, h254, h257, hc23, hlam, hphi, ht34, ht45, p262_1, u5elo4]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h254, h257, hc23, hlam, hphi, ht34, ht45, p262_1, u5elo4]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h257, hc23, hlam, hphi, ht34, ht45, p262_1, u5elo4]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [h261, hlam, p262_0]
                · have p262_0 := h262c.1
                  have p262_1 := h262c.2.1
                  have p262_2 := h262c.2.2.1
                  have p262_3 := h262c.2.2.2
                  linarith only [hlam, p262_0]
              · rcases h5bigk with h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h254, h257, hc23, hlam, hphi, ht34, ht45, p288_1, u5elo0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h257, hc23, hlam, hphi, ht34, ht45, p288_1, u5elo0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h2, hlam, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h159, hlam, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h0, hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h257, hc23, hlam, hphi, ht34, ht45, p288_1, u5elo1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h0, h2, hlam, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h255, hlam, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h1, hlam, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h254, hlam, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h257, hlam, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h259, hlam, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h261, hc05, hlam, hphi, p288_1, u5elo4]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h254, h257, h261, hc23, hlam, hphi, ht34, ht45, p288_1, u5elo4]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h257, h261, hc23, hlam, hphi, ht34, ht45, p288_1, u5elo4]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hlam, p288_0]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h261, hlam, p288_1]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h0, h254, h257, hc23, hlam, hphi, ht34, ht45, p288_1, u5elo4]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h254, h257, hc23, hlam, hphi, ht34, ht45, p288_1, u5elo4]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [h257, hc23, hlam, hphi, ht34, ht45, p288_1, u5elo4]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hc35, hlam, hphi, p288_1, u5elo4]
                · have p288_0 := h288c.1
                  have p288_1 := h288c.2.1
                  have p288_2 := h288c.2.2.1
                  have p288_3 := h288c.2.2.2
                  linarith only [hlam, p288_0]
      · linarith only [h1, h254, hc12, hlam, hphi, u2elo0]

end R2N4
