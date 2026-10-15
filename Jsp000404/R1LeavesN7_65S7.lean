import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_25_L_0_M_LI_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2elo := hb2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
    · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
      · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
        · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
          · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
            · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
              · rcases h5bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hc15, hlam, hphi, p11_1, u5elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hc25, hlam, hphi, p11_1, u5elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hc35, hlam, hphi, p11_1, u5elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hc45, hlam, hphi, p11_1, u5elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h1, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hc25, hlam, hphi, p11_1, u5elo1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h1, h10, hc45, hlam, hphi, p11_1, u5elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h1, hc45, hlam, hphi, p11_1, u5elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h2, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h6, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h10, hc45, hlam, hphi, p11_1, u5elo2]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h5, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11_1, u2elo1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h3, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h7, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h8, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hc45, hlam, hphi, p11_1, u5elo3]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h4, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hc15, hlam, hphi, p11_1, u5elo4]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h9, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h10, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
              · rcases h5bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hlam, p37_0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h10, h6, h9, hc34, hlam, hphi, ht45, p37_1, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h10, h9, hc34, hlam, hphi, ht45, p37_1, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hc35, hlam, hphi, p37_1, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h10, hc34, hlam, hphi, ht45, p37_1, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h1, hlam, p37_0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hlam, p37_0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h10, h9, hc34, hlam, hphi, ht45, p37_1, u5elo1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h1, hc35, hlam, hphi, p37_1, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h1, h10, hc34, hlam, hphi, ht45, p37_1, u5elo0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h2, hlam, p37_1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h6, hlam, p37_1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hlam, p37_0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h10, h5, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p37_1, u2elo1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h10, h5, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p37_1, u2elo1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h3, hlam, p37_1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h7, hlam, p37_1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h8, hlam, p37_0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hlam, p37_0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h10, hlam, p37_0]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h4, hlam, p37_1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hc15, hlam, hphi, p37_1, u5elo4]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h9, hlam, p37_1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [h10, h5, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p37_1, u2elo1]
                · have p37_0 := h37c.1
                  have p37_1 := h37c.2.1
                  have p37_2 := h37c.2.2.1
                  have p37_3 := h37c.2.2.2
                  linarith only [hlam, p37_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
              · linarith only [h5, h63, h8, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · rcases h5bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [hlam, p65_0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [hc15, hlam, hphi, p65_1, u5elo0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [hc25, hlam, hphi, p65_1, u5elo0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [hc35, hlam, hphi, p65_1, u5elo0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h9, hc24, hlam, hphi, ht45, p65_1, u5elo0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h1, hlam, p65_0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [hlam, p65_0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [hc25, hlam, hphi, p65_1, u5elo1]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h1, hc35, hlam, hphi, p65_1, u5elo0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h1, h9, hc24, hlam, hphi, ht45, p65_1, u5elo0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h2, hlam, p65_1]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h6, hlam, p65_1]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [hlam, p65_0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h63, hc34, hlam, hphi, ht45, p65_1, u5elo2]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h9, hlam, p65_0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h3, hlam, p65_1]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h7, hlam, p65_1]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h8, hlam, p65_0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [hlam, p65_0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h63, hlam, p65_0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h4, hlam, p65_1]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [hc15, hlam, hphi, p65_1, u5elo4]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h4, hc25, hlam, hphi, p65_1, u5elo0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [h4, h63, hc34, hlam, hphi, ht45, p65_1, u5elo0]
                · have p65_0 := h65c.1
                  have p65_1 := h65c.2.1
                  have p65_2 := h65c.2.2.1
                  have p65_3 := h65c.2.2.2
                  linarith only [hlam, p65_0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h91 | h91
            · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
              · rcases h5bigk with h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [hlam, p93_0]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h7, h8, hc23, hlam, hphi, ht34, ht45, p93_1, u5elo0]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [hc25, hlam, hphi, p93_1, u5elo0]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h8, hc23, hlam, hphi, ht34, ht45, p93_1, u5elo0]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [hc45, hlam, hphi, p93_1, u5elo0]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h1, hlam, p93_0]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [hlam, p93_0]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h91, hc45, hlam, hphi, p93_1, u5elo1]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h1, h8, hc23, hlam, hphi, ht34, ht45, p93_1, u5elo0]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h1, hc45, hlam, hphi, p93_1, u5elo0]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h2, hlam, p93_1]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h6, hlam, p93_1]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [hlam, p93_0]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h8, hlam, p93_1]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [hc45, hlam, hphi, p93_1, u5elo2]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h3, hlam, p93_1]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h7, hlam, p93_1]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [hc25, hlam, hphi, p93_1, u5elo3]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [hlam, p93_0]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h5, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p93_1, u2elo1]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h4, hlam, p93_1]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [hc15, hlam, hphi, p93_1, u5elo4]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h91, hlam, p93_1]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [h92, hlam, p93_1]
                · have p93_0 := h93c.1
                  have p93_1 := h93c.2.1
                  have p93_2 := h93c.2.2.1
                  have p93_3 := h93c.2.2.2
                  linarith only [hlam, p93_0]
              · linarith only [h8, h91, h92, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h120 | h120
              · rcases h5bigk with h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hc15, hlam, hphi, p121_1, u5elo0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hc25, hlam, hphi, p121_1, u5elo0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h120, h91, hc24, hlam, hphi, ht45, p121_1, u5elo0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h91, hc24, hlam, hphi, ht45, p121_1, u5elo0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h1, hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hc25, hlam, hphi, p121_1, u5elo1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h1, h120, h91, hc24, hlam, hphi, ht45, p121_1, u5elo0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h1, h91, hc24, hlam, hphi, ht45, p121_1, u5elo0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h2, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h6, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h8, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h91, hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h3, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h7, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h8, hc23, hlam, hphi, ht34, ht45, p121_1, u5elo3]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hlam, p121_0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h5, h7, h91, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p121_1, u2elo1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h4, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hc15, hlam, hphi, p121_1, u5elo4]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h4, h8, hc23, hlam, hphi, ht34, ht45, p121_1, u5elo0]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [h120, hlam, p121_1]
                · have p121_0 := h121c.1
                  have p121_1 := h121c.2.1
                  have p121_2 := h121c.2.2.1
                  have p121_3 := h121c.2.2.2
                  linarith only [hlam, p121_0]
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
                  linarith only [h8, hc23, hlam, hphi, ht34, ht45, p147_1, u5elo0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [hc35, hlam, hphi, p147_1, u5elo0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h120, hc34, hlam, hphi, ht45, p147_1, u5elo0]
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
                  linarith only [h8, hc23, hlam, hphi, ht34, ht45, p147_1, u5elo1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h1, hc35, hlam, hphi, p147_1, u5elo0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h1, h120, h8, hc23, hlam, hphi, ht34, ht45, p147_1, u5elo0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h2, hlam, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h6, hlam, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h8, hlam, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h91, hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h3, hlam, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h7, hlam, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h8, hc23, hlam, hphi, ht34, ht45, p147_1, u5elo3]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h120, hlam, p147_0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h4, hlam, p147_1]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h4, hc15, hlam, hphi, p147_1, u5elo0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h4, h8, hc23, hlam, hphi, ht34, ht45, p147_1, u5elo0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [h4, hc35, hlam, hphi, p147_1, u5elo0]
                · have p147_0 := h147c.1
                  have p147_1 := h147c.2.1
                  have p147_2 := h147c.2.2.1
                  have p147_3 := h147c.2.2.2
                  linarith only [hlam, p147_0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h173 | h173
          · linarith only [h173, h5, h7, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h175 | h175
            · rcases m.htr 3 4 5 (by decide) (by decide) with h176 | h176
              · rcases h5bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h7, hc13, hlam, hphi, ht34, ht45, p177_1, u5elo0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h173, hc23, hlam, hphi, ht34, ht45, p177_1, u5elo0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hc35, hlam, hphi, p177_1, u5elo0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hc45, hlam, hphi, p177_1, u5elo0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h1, hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h173, hc23, hlam, hphi, ht34, ht45, p177_1, u5elo1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h7, hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hc45, hlam, hphi, p177_1, u5elo1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h2, hlam, p177_1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h6, hlam, p177_1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h173, hlam, p177_1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hc45, hlam, hphi, p177_1, u5elo2]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h3, hlam, p177_1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h3, hc15, hlam, hphi, p177_1, u5elo0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h3, hc25, hlam, hphi, p177_1, u5elo0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hlam, p177_0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h3, hc45, hlam, hphi, p177_1, u5elo0]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h4, hlam, p177_1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h5, h7, hc23, hlam, hphi, ht34, ht45, p177_1, u5elo4]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h175, hlam, p177_1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [h176, hlam, p177_1]
                · have p177_0 := h177c.1
                  have p177_1 := h177c.2.1
                  have p177_2 := h177c.2.2.1
                  have p177_3 := h177c.2.2.2
                  linarith only [hlam, p177_0]
              · linarith only [h175, h176, h6, h7, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h204 | h204
              · rcases h5bigk with h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c | h205c
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [hlam, p205_0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [hc15, hlam, hphi, p205_1, u5elo0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [hc25, hlam, hphi, p205_1, u5elo0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h6, h7, hc25, hlam, hphi, p205_1, u5elo0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h175, hc24, hlam, hphi, ht45, p205_1, u5elo0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h1, hlam, p205_0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [hlam, p205_0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [hc25, hlam, hphi, p205_1, u5elo1]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h7, hlam, p205_0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h175, h3, h7, hc24, hlam, hphi, ht45, p205_1, u5elo0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h2, hlam, p205_1]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h6, hlam, p205_1]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [hlam, p205_0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h173, hlam, p205_1]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h175, hlam, p205_0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h3, hlam, p205_1]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h3, hc15, hlam, hphi, p205_1, u5elo0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h173, h3, hc23, hlam, hphi, ht34, ht45, p205_1, u5elo0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [hlam, p205_0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h175, h3, hc24, hlam, hphi, ht45, p205_1, u5elo0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h4, hlam, p205_1]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h173, h204, h6, hc23, hc34, hlam, hphi, p205_1]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h173, h4, hc23, hlam, hphi, ht34, ht45, p205_1, u5elo0]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [h204, hlam, p205_1]
                · have p205_0 := h205c.1
                  have p205_1 := h205c.2.1
                  have p205_2 := h205c.2.2.1
                  have p205_3 := h205c.2.2.2
                  linarith only [hlam, p205_0]
              · rcases h5bigk with h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [hlam, p231_0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h173, h6, hc23, hlam, hphi, ht34, ht45, p231_1, u5elo0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h173, hc23, hlam, hphi, ht34, ht45, p231_1, u5elo0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [hc35, hlam, hphi, p231_1, u5elo0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h204, hc34, hlam, hphi, ht45, p231_1, u5elo0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h1, hlam, p231_0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [hlam, p231_0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h173, hc23, hlam, hphi, ht34, ht45, p231_1, u5elo1]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h7, hlam, p231_0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h204, h7, hlam, p231_1]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h2, hlam, p231_1]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h6, hlam, p231_1]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [hlam, p231_0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h173, hlam, p231_1]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h175, hlam, p231_0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h3, hlam, p231_1]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [hc15, hlam, hphi, p231_1, u5elo3]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h173, h204, h4, hc23, hlam, hphi, ht34, ht45, p231_1, u5elo0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [hlam, p231_0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h204, hlam, p231_0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h4, hlam, p231_1]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h173, h4, h6, hc23, hlam, hphi, ht34, ht45, p231_1, u5elo0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h173, h4, hc23, hlam, hphi, ht34, ht45, p231_1, u5elo0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [h4, hc35, hlam, hphi, p231_1, u5elo0]
                · have p231_0 := h231c.1
                  have p231_1 := h231c.2.1
                  have p231_2 := h231c.2.2.1
                  have p231_3 := h231c.2.2.2
                  linarith only [hlam, p231_0]
      · linarith only [h2, h6, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
      · rcases m.htr 1 3 5 (by decide) (by decide) with h259 | h259
        · rcases m.htr 2 3 5 (by decide) (by decide) with h260 | h260
          · rcases m.htr 2 4 5 (by decide) (by decide) with h261 | h261
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
                  linarith only [hc15, hlam, hphi, p263_1, u5elo0]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h260, h262, hc45, hlam, hphi, p263_1, u5elo0]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h262, hc45, hlam, hphi, p263_1, u5elo0]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [hc45, hlam, hphi, p263_1, u5elo0]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h1, hlam, p263_0]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [hlam, p263_0]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h260, h262, hc45, hlam, hphi, p263_1, u5elo1]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h258, h262, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p263_1, u2elo2]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h258, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p263_1, u2elo2]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h2, hlam, p263_1]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h258, hlam, p263_1]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [hlam, p263_0]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h262, hc45, hlam, hphi, p263_1, u5elo2]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h258, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p263_1, u2elo2]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h3, hlam, p263_1]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h259, hlam, p263_1]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h260, hlam, p263_0]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [hlam, p263_0]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [hc45, hlam, hphi, p263_1, u5elo3]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h4, hlam, p263_1]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [hc15, hlam, hphi, p263_1, u5elo4]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h261, hlam, p263_1]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [h262, hlam, p263_1]
                · have p263_0 := h263c.1
                  have p263_1 := h263c.2.1
                  have p263_2 := h263c.2.2.1
                  have p263_3 := h263c.2.2.2
                  linarith only [hlam, p263_0]
              · linarith only [h258, h261, h262, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h290 | h290
              · linarith only [h258, h260, h261, h290, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
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
                  linarith only [hc15, hlam, hphi, p292_1, u5elo0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h260, hc35, hlam, hphi, p292_1, u5elo0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [hc35, hlam, hphi, p292_1, u5elo0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h261, hc24, hlam, hphi, ht45, p292_1, u5elo0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h1, hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h260, hc35, hlam, hphi, p292_1, u5elo1]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h258, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p292_1, u2elo2]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h258, h261, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p292_1, u2elo2]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h2, hlam, p292_1]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h258, hlam, p292_1]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h290, hc34, hlam, hphi, ht45, p292_1, u5elo2]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h261, hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h3, hlam, p292_1]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h259, hlam, p292_1]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h260, hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h290, hlam, p292_0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h4, hlam, p292_1]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [hc15, hlam, hphi, p292_1, u5elo4]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h4, hc25, hlam, hphi, p292_1, u5elo0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [h290, h4, hc34, hlam, hphi, ht45, p292_1, u5elo0]
                · have p292_0 := h292c.1
                  have p292_1 := h292c.2.1
                  have p292_2 := h292c.2.2.1
                  have p292_3 := h292c.2.2.2
                  linarith only [hlam, p292_0]
          · linarith only [h260, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h258, h259, h3, h5, hc25, hlam, hphi, u5elo0]
      · linarith only [h2, h258, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h321 | h321
    · rcases m.htr 1 2 5 (by decide) (by decide) with h322 | h322
      · rcases m.htr 1 3 5 (by decide) (by decide) with h323 | h323
        · rcases m.htr 2 3 5 (by decide) (by decide) with h324 | h324
          · rcases m.htr 2 4 5 (by decide) (by decide) with h325 | h325
            · linarith only [h1, h322, h325, h4, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h327 | h327
              · linarith only [h3, h327, h4, hlam]
              · rcases h5bigk with h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [hlam, p329_0]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h322, hc25, hlam, hphi, p329_1, u5elo0]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h4, hc25, hlam, hphi, p329_1, u5elo4]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h327, h4, hc34, hlam, hphi, ht45, p329_1, u5elo4]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h4, hlam, p329_0]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h1, hlam, p329_0]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [hlam, p329_0]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [hc25, hlam, hphi, p329_1, u5elo1]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h1, h327, h4, hc34, hlam, hphi, ht45, p329_1, u5elo4]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h1, h4, hlam, p329_1]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h2, hlam, p329_1]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h322, hlam, p329_1]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [hlam, p329_0]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h327, hc34, hlam, hphi, ht45, p329_1, u5elo2]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h325, hlam, p329_0]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h3, hlam, p329_1]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h323, hlam, p329_1]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h324, hlam, p329_0]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [hlam, p329_0]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h327, hlam, p329_0]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [hc05, hlam, hphi, p329_1, u5elo4]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [hc15, hlam, hphi, p329_1, u5elo4]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h324, h327, hc34, hlam, hphi, ht45, p329_1, u5elo4]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [h327, hc34, hlam, hphi, ht45, p329_1, u5elo4]
                · have p329_0 := h329c.1
                  have p329_1 := h329c.2.1
                  have p329_2 := h329c.2.2.1
                  have p329_3 := h329c.2.2.2
                  linarith only [hlam, p329_0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h355 | h355
            · linarith only [h1, h323, h324, h355, h4, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h357 | h357
              · linarith only [h1, h323, h357, h4, hlam]
              · rcases h5bigk with h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c | h359c
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [hlam, p359_0]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h323, h324, h4, hc23, hc45, hlam, hphi, ht34, p359_1]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [hc25, hlam, hphi, p359_1, u5elo0]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h324, hc23, hlam, hphi, ht34, ht45, p359_1, u5elo0]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h4, hlam, p359_0]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h1, hlam, p359_0]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [hlam, p359_0]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [hc25, hlam, hphi, p359_1, u5elo1]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h1, h324, h4, hc23, hlam, hphi, ht34, ht45, p359_1, u5elo4]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h1, h4, hlam, p359_1]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h2, hlam, p359_1]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h322, hlam, p359_1]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [hlam, p359_0]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h324, hlam, p359_1]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h355, hlam, p359_0]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h3, hlam, p359_1]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h323, hlam, p359_1]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h0, h323, h324, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p359_1]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [hlam, p359_0]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h357, hlam, p359_0]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [hc05, hlam, hphi, p359_1, u5elo4]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [hc15, hlam, hphi, p359_1, u5elo4]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h324, hc23, hlam, hphi, ht34, ht45, p359_1, u5elo4]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [h324, hc23, hlam, hphi, ht34, ht45, p359_1, u5elo4]
                · have p359_0 := h359c.1
                  have p359_1 := h359c.2.1
                  have p359_2 := h359c.2.2.1
                  have p359_3 := h359c.2.2.2
                  linarith only [hlam, p359_0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h385 | h385
          · linarith only [h321, h323, h385, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h387 | h387
            · linarith only [h2, h387, h4, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h389 | h389
              · linarith only [h3, h389, h4, hlam]
              · rcases h5bigk with h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [hlam, p391_0]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h322, hc25, hlam, hphi, p391_1, u5elo0]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h4, hc25, hlam, hphi, p391_1, u5elo4]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h4, hc35, hlam, hphi, p391_1, u5elo4]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h4, hlam, p391_0]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h1, hlam, p391_0]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [hlam, p391_0]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [hc25, hlam, hphi, p391_1, u5elo1]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h323, hlam, p391_0]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h4, hc05, hlam, hphi, p391_1, u5elo1]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h2, hlam, p391_1]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h322, hlam, p391_1]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [hlam, p391_0]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h385, hlam, p391_1]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h387, hlam, p391_0]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h3, hlam, p391_1]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [hc15, hlam, hphi, p391_1, u5elo3]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h3, h385, hc23, hlam, hphi, ht34, ht45, p391_1, u5elo0]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [hlam, p391_0]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h389, hlam, p391_0]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [hc05, hlam, hphi, p391_1, u5elo4]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h322, h385, hc23, hlam, hphi, ht34, ht45, p391_1, u5elo4]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h385, hc23, hlam, hphi, ht34, ht45, p391_1, u5elo4]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [h321, h323, hc23, hlam, hphi, ht34, ht45, p391_1, u5elo4]
                · have p391_0 := h391c.1
                  have p391_1 := h391c.2.1
                  have p391_2 := h391c.2.2.1
                  have p391_3 := h391c.2.2.2
                  linarith only [hlam, p391_0]
      · linarith only [h2, h322, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h418 | h418
      · rcases m.htr 1 3 5 (by decide) (by decide) with h419 | h419
        · rcases m.htr 2 3 5 (by decide) (by decide) with h420 | h420
          · rcases m.htr 2 4 5 (by decide) (by decide) with h421 | h421
            · linarith only [h2, h4, h421, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h423 | h423
              · linarith only [h321, h4, h418, h420, h423, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases h5bigk with h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hc15, hlam, hphi, p425_1, u5elo0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h420, hc35, hlam, hphi, p425_1, u5elo0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hc35, hlam, hphi, p425_1, u5elo0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h4, hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h1, hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h420, hc35, hlam, hphi, p425_1, u5elo1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h321, h418, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p425_1, u2elo2]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h321, h4, h418, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p425_1, u2elo2]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h2, hlam, p425_1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h418, hlam, p425_1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h423, hc34, hlam, hphi, ht45, p425_1, u5elo2]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h421, hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h3, hlam, p425_1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h419, hlam, p425_1]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h420, hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h423, hlam, p425_0]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hc05, hlam, hphi, p425_1, u5elo4]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h418, h420, h423, hc34, hlam, hphi, ht45, p425_1, u5elo4]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h420, h423, hc34, hlam, hphi, ht45, p425_1, u5elo4]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [h423, hc34, hlam, hphi, ht45, p425_1, u5elo4]
                · have p425_0 := h425c.1
                  have p425_1 := h425c.2.1
                  have p425_2 := h425c.2.2.1
                  have p425_3 := h425c.2.2.2
                  linarith only [hlam, p425_0]
          · linarith only [h321, h420, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h3, h321, h418, h419, hc25, hlam, hphi, u5elo0]
      · linarith only [h2, h418, hc12, hlam, hphi, u2elo0]

end R2N4
