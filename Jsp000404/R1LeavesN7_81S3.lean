import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_13_25_L_0_L_I_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · rcases h5bigk with h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc15, hlam, hphi, p6_1, u5elo0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc25, hlam, hphi, p6_1, u5elo0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h5, hc45, hlam, hphi, p6_1, u5elo0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc45, hlam, hphi, p6_1, u5elo0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h1, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc25, hlam, hphi, p6_1, u5elo1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h5, hc45, hlam, hphi, p6_1, u5elo1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p6_1, u1elo0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc05, hlam, hphi, p6_1, u5elo2]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc15, hlam, hphi, p6_1, u5elo2]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h5, hc45, hlam, hphi, p6_1, u5elo2]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc45, hlam, hphi, p6_1, u5elo2]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h2, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h3, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h1, h3, hc25, hlam, hphi, p6_1, u5elo0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h1, h3, hc45, hlam, hphi, p6_1, u5elo0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc05, hlam, hphi, p6_1, u5elo4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h4, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, p6_1, u1elo0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h5, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
            · linarith only [h0, h4, h5, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h33 | h33
            · linarith only [h3, h33, h4, hlam]
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
                linarith only [h33, hc34, hlam, hphi, ht45, p35_1, u5elo0]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [h4, hc14, hlam, hphi, ht45, p35_1, u5elo0]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [h1, hlam, p35_0]
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
                linarith only [h33, hc34, hlam, hphi, ht45, p35_1, u5elo1]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [h4, hlam, p35_1]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [hc05, hlam, hphi, p35_1, u5elo2]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [hc15, hlam, hphi, p35_1, u5elo2]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [hlam, p35_0]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [h33, hc34, hlam, hphi, ht45, p35_1, u5elo2]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [h4, hc14, hlam, hphi, ht45, p35_1, u5elo2]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [h2, hlam, p35_0]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [h3, hlam, p35_0]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [h1, h3, hc25, hlam, hphi, p35_1, u5elo0]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [hlam, p35_0]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [h33, hlam, p35_1]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [hc05, hlam, hphi, p35_1, u5elo4]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [hc15, hlam, hphi, p35_1, u5elo4]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [hc25, hlam, hphi, p35_1, u5elo4]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [h33, hc34, hlam, hphi, ht45, p35_1, u5elo4]
              · have p35_0 := h35c.1
                have p35_1 := h35c.2.1
                have p35_2 := h35c.2.2.1
                have p35_3 := h35c.2.2.2
                linarith only [hlam, p35_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
          · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
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
                linarith only [h3, hc13, hlam, hphi, ht34, ht45, p63_1, u5elo0]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [hc45, hlam, hphi, p63_1, u5elo0]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [h1, hlam, p63_0]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [hlam, p63_0]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [hc25, hlam, hphi, p63_1, u5elo1]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [h3, hlam, p63_1]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [hc45, hlam, hphi, p63_1, u5elo1]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [hc05, hlam, hphi, p63_1, u5elo2]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [hc15, hlam, hphi, p63_1, u5elo2]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [hlam, p63_0]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [h3, hc13, hlam, hphi, ht34, ht45, p63_1, u5elo2]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [hc45, hlam, hphi, p63_1, u5elo2]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [h2, hlam, p63_0]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [h2, h3, hc13, hlam, hphi, ht34, ht45, p63_1, u5elo0]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [h2, hc25, hlam, hphi, p63_1, u5elo0]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [hlam, p63_0]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [h2, hc45, hlam, hphi, p63_1, u5elo0]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [hc05, hlam, hphi, p63_1, u5elo4]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [h61, hlam, p63_0]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [h61, hc25, hlam, hphi, p63_1, u5elo1]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [h62, hlam, p63_0]
              · have p63_0 := h63c.1
                have p63_1 := h63c.2.1
                have p63_2 := h63c.2.2.1
                have p63_3 := h63c.2.2.2
                linarith only [hlam, p63_0]
            · linarith only [h0, h61, h62, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h90 | h90
            · rcases h5bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hc15, hlam, hphi, p91_1, u5elo0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hc25, hlam, hphi, p91_1, u5elo0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h61, h90, hc14, hlam, hphi, ht45, p91_1, u5elo0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h61, hc14, hlam, hphi, ht45, p91_1, u5elo0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h1, hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hc25, hlam, hphi, p91_1, u5elo1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h3, hlam, p91_1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h61, hlam, p91_1]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h2, h3, hc13, hlam, hphi, ht34, ht45, p91_1, u5elo2]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h3, hc13, hlam, hphi, ht34, ht45, p91_1, u5elo2]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h3, hc13, hlam, hphi, ht34, ht45, p91_1, u5elo2]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h61, hc14, hlam, hphi, ht45, p91_1, u5elo2]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h2, hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h2, h3, hc13, hlam, hphi, ht34, ht45, p91_1, u5elo0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h2, hc25, hlam, hphi, p91_1, u5elo0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h2, h61, hc14, hlam, hphi, ht45, p91_1, u5elo0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hc05, hlam, hphi, p91_1, u5elo4]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h3, hc13, hlam, hphi, ht34, ht45, p91_1, u5elo4]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h2, h90, hc25, hlam, hphi, p91_1, u5elo0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [h90, hlam, p91_0]
              · have p91_0 := h91c.1
                have p91_1 := h91c.2.1
                have p91_2 := h91c.2.2.1
                have p91_3 := h91c.2.2.2
                linarith only [hlam, p91_0]
            · rcases h5bigk with h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c | h117c
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [hlam, p117_0]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h3, hc13, hlam, hphi, ht34, ht45, p117_1, u5elo0]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [hc25, hlam, hphi, p117_1, u5elo0]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [hc35, hlam, hphi, p117_1, u5elo0]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h90, hc34, hlam, hphi, ht45, p117_1, u5elo0]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h1, hlam, p117_0]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [hlam, p117_0]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [hc25, hlam, hphi, p117_1, u5elo1]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h3, hlam, p117_1]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h61, hlam, p117_1]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [hc05, hlam, hphi, p117_1, u5elo2]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h3, hc13, hlam, hphi, ht34, ht45, p117_1, u5elo2]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [hlam, p117_0]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h3, hc13, hlam, hphi, ht34, ht45, p117_1, u5elo2]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h3, h90, hc13, hlam, hphi, ht34, ht45, p117_1, u5elo2]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h2, hlam, p117_0]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h2, h3, hc13, hlam, hphi, ht34, ht45, p117_1, u5elo0]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h2, hc25, hlam, hphi, p117_1, u5elo0]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [hlam, p117_0]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h90, hlam, p117_1]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [hc05, hlam, hphi, p117_1, u5elo4]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h3, hc13, hlam, hphi, ht34, ht45, p117_1, u5elo4]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [hc25, hlam, hphi, p117_1, u5elo4]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [h3, hc13, hlam, hphi, ht34, ht45, p117_1, u5elo4]
              · have p117_0 := h117c.1
                have p117_1 := h117c.2.1
                have p117_2 := h117c.2.2.1
                have p117_3 := h117c.2.2.2
                linarith only [hlam, p117_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h143 | h143
        · linarith only [h1, h143, h2, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
          · rcases m.htr 3 4 5 (by decide) (by decide) with h146 | h146
            · rcases h5bigk with h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hc15, hlam, hphi, p147_1, u5elo0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h2, hc25, hlam, hphi, p147_1, u5elo3]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h2, hlam, p147_1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h2, hc45, hlam, hphi, p147_1, u5elo3]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h1, hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hc25, hlam, hphi, p147_1, u5elo1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h143, hlam, p147_1]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h0, h145, hc45, hlam, hphi, ht01, ht0b, ht5b, p147_1, u1elo0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hc05, hlam, hphi, p147_1, u5elo2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hc15, hlam, hphi, p147_1, u5elo2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hc35, hlam, hphi, p147_1, u5elo2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hc45, hlam, hphi, p147_1, u5elo2]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h1, h143, hc13, hlam, hphi, ht34, ht45, p147_1, u5elo3]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h143, hc13, hlam, hphi, ht34, ht45, p147_1, u5elo3]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hc25, hlam, hphi, p147_1, u5elo3]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hc45, hlam, hphi, p147_1, u5elo3]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h1, h143, hc13, hlam, hphi, ht34, ht45, p147_1, u5elo4]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h145, hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h1, h145, hc25, hlam, hphi, p147_1, u5elo0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [h146, hlam, p147_0]
              · have p147_0 := h147c.1
                have p147_1 := h147c.2.1
                have p147_2 := h147c.2.2.1
                have p147_3 := h147c.2.2.2
                linarith only [hlam, p147_0]
            · linarith only [h0, h145, h146, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h174 | h174
            · rcases h5bigk with h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [hlam, p175_0]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h2, hc15, hlam, hphi, p175_1, u5elo3]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h2, hc25, hlam, hphi, p175_1, u5elo3]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h2, hlam, p175_1]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h2, hc45, hlam, hphi, p175_1, u5elo3]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h1, hlam, p175_0]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [hlam, p175_0]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [hc25, hlam, hphi, p175_1, u5elo1]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h143, hlam, p175_1]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h145, hlam, p175_1]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [hc05, hlam, hphi, p175_1, u5elo2]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [hc15, hlam, hphi, p175_1, u5elo2]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [hlam, p175_0]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [hc35, hlam, hphi, p175_1, u5elo2]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h145, hc14, hlam, hphi, ht45, p175_1, u5elo2]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h1, h143, hc13, hlam, hphi, ht34, ht45, p175_1, u5elo3]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h143, hc13, hlam, hphi, ht34, ht45, p175_1, u5elo3]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [hc25, hlam, hphi, p175_1, u5elo3]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [hlam, p175_0]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h145, hc14, hlam, hphi, ht45, p175_1, u5elo3]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h1, h143, h174, hc13, hc34, hlam, hphi, p175_1]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h143, hc13, hlam, hphi, ht34, ht45, p175_1, u5elo4]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h174, hc25, hlam, hphi, p175_1, u5elo3]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [h174, hlam, p175_0]
              · have p175_0 := h175c.1
                have p175_1 := h175c.2.1
                have p175_2 := h175c.2.2.1
                have p175_3 := h175c.2.2.2
                linarith only [hlam, p175_0]
            · rcases h5bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [hlam, p201_0]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h143, hc13, hlam, hphi, ht34, ht45, p201_1, u5elo0]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [hc25, hlam, hphi, p201_1, u5elo0]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h2, hlam, p201_1]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h174, h2, hlam, p201_1]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h1, hlam, p201_0]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [hlam, p201_0]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [hc25, hlam, hphi, p201_1, u5elo1]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h143, hlam, p201_1]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h145, hlam, p201_1]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [hc05, hlam, hphi, p201_1, u5elo2]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [hc15, hlam, hphi, p201_1, u5elo2]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [hlam, p201_0]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [hc35, hlam, hphi, p201_1, u5elo2]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h174, hc34, hlam, hphi, ht45, p201_1, u5elo2]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h1, h143, hc13, hlam, hphi, ht34, ht45, p201_1, u5elo3]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h143, hc13, hlam, hphi, ht34, ht45, p201_1, u5elo3]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h174, hc25, hlam, hphi, p201_1, u5elo4]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [hlam, p201_0]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h174, hlam, p201_1]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h1, h143, hc13, hlam, hphi, ht34, ht45, p201_1, u5elo4]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [h143, hc13, hlam, hphi, ht34, ht45, p201_1, u5elo4]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [hc25, hlam, hphi, p201_1, u5elo4]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [hc35, hlam, hphi, p201_1, u5elo4]
              · have p201_0 := h201c.1
                have p201_1 := h201c.2.1
                have p201_2 := h201c.2.2.1
                have p201_3 := h201c.2.2.2
                linarith only [hlam, p201_0]
    · linarith only [h0, h1, hc14, hlam, hphi, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h228 | h228
    · rcases m.htr 0 3 5 (by decide) (by decide) with h229 | h229
      · rcases m.htr 1 3 5 (by decide) (by decide) with h230 | h230
        · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
          · rcases m.htr 3 4 5 (by decide) (by decide) with h232 | h232
            · rcases h5bigk with h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [hlam, p233_0]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h230, h232, hc45, hlam, hphi, p233_1, u5elo0]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h0, h228, hc25, hlam, hphi, ht01, ht0b, ht5b, p233_1, u1elo3]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h0, h228, hc35, hlam, hphi, ht01, ht0b, ht5b, p233_1, u1elo3]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h0, h228, hc45, hlam, hphi, ht01, ht0b, ht5b, p233_1, u1elo3]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h228, hlam, p233_0]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [hlam, p233_0]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h0, h228, hc25, hlam, hphi, ht01, ht0b, ht5b, p233_1, u1elo3]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h0, h228, h232, hc45, hlam, hphi, ht01, ht0b, ht5b, p233_1, u1elo3]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h0, h228, hc45, hlam, hphi, ht01, ht0b, ht5b, p233_1, u1elo3]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [hc05, hlam, hphi, p233_1, u5elo2]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [hc15, hlam, hphi, p233_1, u5elo2]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [hlam, p233_0]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h232, hc45, hlam, hphi, p233_1, u5elo2]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [hc45, hlam, hphi, p233_1, u5elo2]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h229, hlam, p233_0]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h230, hlam, p233_0]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h230, hc25, hlam, hphi, ht01, ht0b, ht5b, p233_1, u1elo2]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [hlam, p233_0]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h0, h228, h230, hc45, hlam, hphi, ht01, ht0b, ht5b, p233_1, u1elo3]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [hc05, hlam, hphi, p233_1, u5elo4]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h231, hlam, p233_0]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h228, h230, h232, hc25, hlam, hphi, p233_1, u5elo0]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [h232, hlam, p233_0]
              · have p233_0 := h233c.1
                have p233_1 := h233c.2.1
                have p233_2 := h233c.2.2.1
                have p233_3 := h233c.2.2.2
                linarith only [hlam, p233_0]
            · linarith only [h0, h228, h231, h232, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
          · linarith only [h0, h231, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h261 | h261
          · rcases m.htr 3 4 5 (by decide) (by decide) with h262 | h262
            · rcases h5bigk with h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [hlam, p263_0]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h0, h228, h230, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p263_1, u1elo3]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h0, h228, hc25, hlam, hphi, ht01, ht0b, ht5b, p263_1, u1elo3]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h0, h228, h230, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p263_1, u1elo3]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h0, h228, hc45, hlam, hphi, ht01, ht0b, ht5b, p263_1, u1elo3]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h228, hlam, p263_0]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [hlam, p263_0]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [hc25, hlam, hphi, p263_1, u5elo1]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h230, hlam, p263_1]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h0, h228, hc45, hlam, hphi, ht01, ht0b, ht5b, p263_1, u1elo3]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [hc05, hlam, hphi, p263_1, u5elo2]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [hc15, hlam, hphi, p263_1, u5elo2]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [hlam, p263_0]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h230, hc13, hlam, hphi, ht34, ht45, p263_1, u5elo2]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [hc45, hlam, hphi, p263_1, u5elo2]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h229, hlam, p263_0]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h229, h230, hc13, hlam, hphi, ht34, ht45, p263_1, u5elo0]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h0, h228, h229, hc25, hlam, hphi, ht01, ht0b, ht5b, p263_1, u1elo3]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [hlam, p263_0]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h0, h228, h229, hc45, hlam, hphi, ht01, ht0b, ht5b, p263_1, u1elo3]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [hc05, hlam, hphi, p263_1, u5elo4]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h261, hlam, p263_0]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h261, hc25, hlam, hphi, p263_1, u5elo1]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [h262, hlam, p263_0]
              · have p263_0 := h263c.1
                have p263_1 := h263c.2.1
                have p263_2 := h263c.2.2.1
                have p263_3 := h263c.2.2.2
                linarith only [hlam, p263_0]
            · linarith only [h0, h228, h261, h262, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
          · linarith only [h0, h261, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h291 | h291
        · linarith only [h0, h228, h229, h291, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
          · rcases m.htr 3 4 5 (by decide) (by decide) with h294 | h294
            · rcases h5bigk with h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hlam, p295_0]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hc15, hlam, hphi, p295_1, u5elo0]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [h0, h228, hc25, hlam, hphi, ht01, ht0b, ht5b, p295_1, u1elo3]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [h229, hlam, p295_1]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [h0, h228, hc45, hlam, hphi, ht01, ht0b, ht5b, p295_1, u1elo3]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [h228, hlam, p295_0]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hlam, p295_0]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hc25, hlam, hphi, p295_1, u5elo1]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [h291, hlam, p295_1]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [h0, h228, hc45, hlam, hphi, ht01, ht0b, ht5b, p295_1, u1elo3]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hc05, hlam, hphi, p295_1, u5elo2]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hc15, hlam, hphi, p295_1, u5elo2]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hlam, p295_0]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hc35, hlam, hphi, p295_1, u5elo2]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hc45, hlam, hphi, p295_1, u5elo2]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [h228, h291, hc13, hlam, hphi, ht34, ht45, p295_1, u5elo3]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [h291, hc13, hlam, hphi, ht34, ht45, p295_1, u5elo3]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hc25, hlam, hphi, p295_1, u5elo3]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hlam, p295_0]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hc45, hlam, hphi, p295_1, u5elo3]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [h228, h291, hc13, hlam, hphi, ht34, ht45, p295_1, u5elo4]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [h293, hlam, p295_0]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [h228, h293, hc25, hlam, hphi, p295_1, u5elo0]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [h294, hlam, p295_0]
              · have p295_0 := h295c.1
                have p295_1 := h295c.2.1
                have p295_2 := h295c.2.2.1
                have p295_3 := h295c.2.2.2
                linarith only [hlam, p295_0]
            · linarith only [h0, h228, h293, h294, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
          · linarith only [h0, h293, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h323 | h323
      · rcases m.htr 1 3 5 (by decide) (by decide) with h324 | h324
        · rcases m.htr 1 4 5 (by decide) (by decide) with h325 | h325
          · rcases m.htr 3 4 5 (by decide) (by decide) with h326 | h326
            · rcases h5bigk with h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h228, hlam, p327_1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h228, hc25, hlam, hphi, p327_1, u5elo1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h228, hc35, hlam, hphi, p327_1, u5elo1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h228, hc45, hlam, hphi, p327_1, u5elo1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hc05, hlam, hphi, p327_1, u5elo1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hc25, hlam, hphi, p327_1, u5elo1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h326, hc45, hlam, hphi, p327_1, u5elo1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hc45, hlam, hphi, p327_1, u5elo1]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p327_1, u5elo2]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hc15, hlam, hphi, p327_1, u5elo2]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h326, hc45, hlam, hphi, p327_1, u5elo2]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hc45, hlam, hphi, p327_1, u5elo2]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h323, hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h324, hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hc25, hlam, hphi, p327_1, u5elo3]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h324, hc45, hlam, hphi, ht01, ht0b, ht5b, p327_1, u1elo2]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hc05, hlam, hphi, p327_1, u5elo4]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h325, hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h324, h326, hc25, hlam, hphi, ht01, ht0b, ht5b, p327_1, u1elo2]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [h326, hlam, p327_0]
              · have p327_0 := h327c.1
                have p327_1 := h327c.2.1
                have p327_2 := h327c.2.2.1
                have p327_3 := h327c.2.2.2
                linarith only [hlam, p327_0]
            · rcases h5bigk with h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c | h353c
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h228, hlam, p353_1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hc25, hlam, hphi, p353_1, u5elo0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hc35, hlam, hphi, p353_1, u5elo0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h228, hc45, hlam, hphi, p353_1, u5elo1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hc05, hlam, hphi, p353_1, u5elo1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hc25, hlam, hphi, p353_1, u5elo1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h326, hc34, hlam, hphi, ht45, p353_1, u5elo1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h326, hc34, hlam, hphi, ht45, p353_1, u5elo1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p353_1, u5elo2]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hc15, hlam, hphi, p353_1, u5elo2]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h326, hc34, hlam, hphi, ht45, p353_1, u5elo2]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h326, hc34, hlam, hphi, ht45, p353_1, u5elo2]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h323, hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h324, hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hc25, hlam, hphi, p353_1, u5elo3]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h326, hlam, p353_1]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h325, hc05, hlam, hphi, ht01, ht0b, ht5b, p353_1, u1elo3]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h325, hlam, p353_0]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h325, hc25, hlam, hphi, ht01, ht0b, ht5b, p353_1, u1elo3]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [h325, hc35, hlam, hphi, ht01, ht0b, ht5b, p353_1, u1elo3]
              · have p353_0 := h353c.1
                have p353_1 := h353c.2.1
                have p353_2 := h353c.2.2.1
                have p353_3 := h353c.2.2.2
                linarith only [hlam, p353_0]
          · linarith only [h0, h325, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
        · linarith only [h228, h323, h324, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h381 | h381
        · rcases m.htr 1 4 5 (by decide) (by decide) with h382 | h382
          · rcases m.htr 3 4 5 (by decide) (by decide) with h383 | h383
            · rcases h5bigk with h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [hlam, p384_0]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h228, hlam, p384_1]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h323, h381, hc25, hlam, hphi, ht01, ht0b, ht5b, p384_1, u1elo2]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h323, hlam, p384_1]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h323, h381, hc45, hlam, hphi, ht01, ht0b, ht5b, p384_1, u1elo2]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [hc05, hlam, hphi, p384_1, u5elo1]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [hlam, p384_0]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [hc25, hlam, hphi, p384_1, u5elo1]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h323, hc03, hlam, hphi, ht34, ht45, p384_1, u5elo1]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [hc45, hlam, hphi, p384_1, u5elo1]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p384_1, u5elo2]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [hc15, hlam, hphi, p384_1, u5elo2]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [hlam, p384_0]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h323, hc03, hlam, hphi, ht34, ht45, p384_1, u5elo2]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [hc45, hlam, hphi, p384_1, u5elo2]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p384_1, u5elo3]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h381, hlam, p384_0]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h381, hc25, hlam, hphi, ht01, ht0b, ht5b, p384_1, u1elo2]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [hlam, p384_0]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h381, hc45, hlam, hphi, ht01, ht0b, ht5b, p384_1, u1elo2]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p384_1, u5elo4]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h382, hlam, p384_0]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h381, h383, hc25, hlam, hphi, ht01, ht0b, ht5b, p384_1, u1elo2]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [h383, hlam, p384_0]
              · have p384_0 := h384c.1
                have p384_1 := h384c.2.1
                have p384_2 := h384c.2.2.1
                have p384_3 := h384c.2.2.2
                linarith only [hlam, p384_0]
            · rcases h5bigk with h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hlam, p410_0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h228, hlam, p410_1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc25, hlam, hphi, p410_1, u5elo0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h323, hlam, p410_1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h323, h383, hlam, p410_1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc05, hlam, hphi, p410_1, u5elo1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hlam, p410_0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc25, hlam, hphi, p410_1, u5elo1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h323, hc03, hlam, hphi, ht34, ht45, p410_1, u5elo1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h323, h383, hc03, hlam, hphi, ht34, ht45, p410_1, u5elo1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p410_1, u5elo2]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hc15, hlam, hphi, p410_1, u5elo2]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hlam, p410_0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h323, hc03, hlam, hphi, ht34, ht45, p410_1, u5elo2]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h323, h383, hc03, hlam, hphi, ht34, ht45, p410_1, u5elo2]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h228, h382, h383, hc01, hlam, hphi, p410_1, u1elo3]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h381, hlam, p410_0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h382, h383, hc25, hlam, hphi, ht01, ht0b, ht5b, p410_1, u1elo3]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hlam, p410_0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h383, hlam, p410_1]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h228, h382, hc01, hlam, hphi, p410_1, u1elo3]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h382, hlam, p410_0]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h382, hc25, hlam, hphi, ht01, ht0b, ht5b, p410_1, u1elo3]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [h323, h382, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p410_1, u1elo3]
              · have p410_0 := h410c.1
                have p410_1 := h410c.2.1
                have p410_2 := h410c.2.2.1
                have p410_3 := h410c.2.2.2
                linarith only [hlam, p410_0]
          · linarith only [h0, h382, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h437 | h437
          · rcases m.htr 3 4 5 (by decide) (by decide) with h438 | h438
            · rcases h5bigk with h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c | h439c
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [hlam, p439_0]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h228, hlam, p439_1]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [hc25, hlam, hphi, p439_1, u5elo0]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h323, hlam, p439_1]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [hc45, hlam, hphi, p439_1, u5elo0]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [hc05, hlam, hphi, p439_1, u5elo1]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [hlam, p439_0]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h381, hc25, hlam, hphi, p439_1, u5elo3]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h381, hlam, p439_1]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h381, hc45, hlam, hphi, p439_1, u5elo3]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p439_1, u5elo2]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [hc15, hlam, hphi, p439_1, u5elo2]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [hlam, p439_0]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h381, hc13, hlam, hphi, ht34, ht45, p439_1, u5elo2]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [hc45, hlam, hphi, p439_1, u5elo2]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p439_1, u5elo3]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p439_1, u5elo3]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [hc25, hlam, hphi, p439_1, u5elo3]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [hlam, p439_0]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [hc45, hlam, hphi, p439_1, u5elo3]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p439_1, u5elo4]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h437, hlam, p439_0]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h437, hc25, hlam, hphi, ht01, ht0b, ht5b, p439_1, u1elo3]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [h438, hlam, p439_0]
              · have p439_0 := h439c.1
                have p439_1 := h439c.2.1
                have p439_2 := h439c.2.2.1
                have p439_3 := h439c.2.2.2
                linarith only [hlam, p439_0]
            · linarith only [h228, h381, h437, h438, hc01, hlam, hphi, u1elo3]
          · linarith only [h0, h437, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]

end R2N4
