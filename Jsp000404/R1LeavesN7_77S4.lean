import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_25_L_I_M_LI_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
        · rcases h5bigk with h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [hlam, p5_0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [hc15, hlam, hphi, p5_1, u5elo0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [hc25, hlam, hphi, p5_1, u5elo0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [hc35, hlam, hphi, p5_1, u5elo0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [hc45, hlam, hphi, p5_1, u5elo0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h0, hlam, p5_0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [hlam, p5_0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h3, hc35, hlam, hphi, p5_1, u5elo1]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h0, hc35, hlam, hphi, p5_1, u5elo0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p5_1, u5elo0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h1, hlam, p5_1]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [hc15, hlam, hphi, p5_1, u5elo2]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [hlam, p5_0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h1, hc35, hlam, hphi, p5_1, u5elo0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h1, hc45, hlam, hphi, p5_1, u5elo0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h2, hlam, p5_1]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [hc15, hlam, hphi, p5_1, u5elo3]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h3, hlam, p5_0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [hlam, p5_0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h1, h3, hc45, hlam, hphi, p5_1, u5elo0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [hc05, hlam, hphi, p5_1, u5elo4]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h1, h4, hc15, hlam, hphi, p5_1, u5elo0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h4, hlam, p5_1]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [h1, h4, hc35, hlam, hphi, p5_1, u5elo0]
          · have p5_0 := h5c.1
            have p5_1 := h5c.2.1
            have p5_2 := h5c.2.2.1
            have p5_3 := h5c.2.2.2
            linarith only [hlam, p5_0]
        · rcases h5bigk with h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hlam, p31_0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hc15, hlam, hphi, p31_1, u5elo0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hc25, hlam, hphi, p31_1, u5elo0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hc35, hlam, hphi, p31_1, u5elo0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [h4, hc24, hlam, hphi, ht45, p31_1, u5elo0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [h0, hlam, p31_0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hlam, p31_0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [h4, hc24, hlam, hphi, ht45, p31_1, u5elo1]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [h0, hc35, hlam, hphi, p31_1, u5elo0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [h0, h4, hc24, hlam, hphi, ht45, p31_1, u5elo0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [h1, hlam, p31_1]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hc15, hlam, hphi, p31_1, u5elo2]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hlam, p31_0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hc35, hlam, hphi, p31_1, u5elo2]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [h4, hlam, p31_0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [h2, hlam, p31_1]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hc15, hlam, hphi, p31_1, u5elo3]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [h3, hlam, p31_0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hlam, p31_0]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [h3, h4, hlam, p31_1]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hc05, hlam, hphi, p31_1, u5elo4]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hc15, hlam, hphi, p31_1, u5elo4]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [h4, hc24, hlam, hphi, ht45, p31_1, u5elo4]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hc35, hlam, hphi, p31_1, u5elo4]
          · have p31_0 := h31c.1
            have p31_1 := h31c.2.1
            have p31_2 := h31c.2.2.1
            have p31_3 := h31c.2.2.2
            linarith only [hlam, p31_0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
        · rcases h5bigk with h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [hlam, p58_0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [hc15, hlam, hphi, p58_1, u5elo0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [hc25, hlam, hphi, p58_1, u5elo0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h3, hc23, hlam, hphi, ht34, ht45, p58_1, u5elo0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [hc45, hlam, hphi, p58_1, u5elo0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h0, hlam, p58_0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [hlam, p58_0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h3, hc23, hlam, hphi, ht34, ht45, p58_1, u5elo1]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h0, h3, hc23, hlam, hphi, ht34, ht45, p58_1, u5elo0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p58_1, u5elo0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h1, hlam, p58_1]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [hc15, hlam, hphi, p58_1, u5elo2]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [hlam, p58_0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h3, hlam, p58_1]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [hc45, hlam, hphi, p58_1, u5elo2]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h2, hlam, p58_1]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h2, hc15, hlam, hphi, p58_1, u5elo0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h2, hc25, hlam, hphi, p58_1, u5elo0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [hlam, p58_0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h2, hc45, hlam, hphi, p58_1, u5elo0]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [hc05, hlam, hphi, p58_1, u5elo4]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h57, hc15, hlam, hphi, p58_1, u5elo2]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h57, hlam, p58_1]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [h3, h57, hlam, p58_1]
          · have p58_0 := h58c.1
            have p58_1 := h58c.2.1
            have p58_2 := h58c.2.2.1
            have p58_3 := h58c.2.2.2
            linarith only [hlam, p58_0]
        · rcases h5bigk with h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [hlam, p84_0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [hc15, hlam, hphi, p84_1, u5elo0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [hc25, hlam, hphi, p84_1, u5elo0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [hc35, hlam, hphi, p84_1, u5elo0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h57, hc24, hlam, hphi, ht45, p84_1, u5elo0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h0, hlam, p84_0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [hlam, p84_0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h3, hc23, hlam, hphi, ht34, ht45, p84_1, u5elo1]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h0, h3, hc23, hlam, hphi, ht34, ht45, p84_1, u5elo0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h0, h57, hc24, hlam, hphi, ht45, p84_1, u5elo0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h1, hlam, p84_1]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [hc15, hlam, hphi, p84_1, u5elo2]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [hlam, p84_0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h3, hlam, p84_1]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h57, hlam, p84_0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h2, hlam, p84_1]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h2, hc15, hlam, hphi, p84_1, u5elo0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h2, hc25, hlam, hphi, p84_1, u5elo0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [hlam, p84_0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h2, h57, hc24, hlam, hphi, ht45, p84_1, u5elo0]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [hc05, hlam, hphi, p84_1, u5elo4]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [hc15, hlam, hphi, p84_1, u5elo4]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h3, hc23, hlam, hphi, ht34, ht45, p84_1, u5elo4]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [h3, hc23, hlam, hphi, ht34, ht45, p84_1, u5elo4]
          · have p84_0 := h84c.1
            have p84_1 := h84c.2.1
            have p84_2 := h84c.2.2.1
            have p84_3 := h84c.2.2.2
            linarith only [hlam, p84_0]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
      · linarith only [h1, h110, h2, hlam]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h112 | h112
        · rcases h5bigk with h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [hlam, p113_0]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [hc15, hlam, hphi, p113_1, u5elo0]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h112, hc45, hlam, hphi, p113_1, u5elo0]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h2, hlam, p113_0]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h2, hc45, hlam, hphi, p113_1, u5elo3]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h0, hlam, p113_0]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [hlam, p113_0]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h110, hc23, hlam, hphi, ht34, ht45, p113_1, u5elo1]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h0, h2, hlam, p113_1]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h0, h2, hc45, hlam, hphi, p113_1, u5elo3]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h1, hlam, p113_1]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [hc15, hlam, hphi, p113_1, u5elo2]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [hlam, p113_0]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h110, hlam, p113_1]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h1, h2, hc45, hlam, hphi, p113_1, u5elo3]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [hc05, hlam, hphi, p113_1, u5elo3]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [hc15, hlam, hphi, p113_1, u5elo3]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h110, hc23, hlam, hphi, ht34, ht45, p113_1, u5elo3]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [hlam, p113_0]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [hc45, hlam, hphi, p113_1, u5elo3]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h1, h110, hc23, hlam, hphi, ht34, ht45, p113_1, u5elo4]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h1, h112, hc15, hlam, hphi, p113_1, u5elo0]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h112, hlam, p113_1]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [h1, h112, h2, hlam, p113_1]
          · have p113_0 := h113c.1
            have p113_1 := h113c.2.1
            have p113_2 := h113c.2.2.1
            have p113_3 := h113c.2.2.2
            linarith only [hlam, p113_0]
        · rcases h5bigk with h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [hlam, p139_0]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h2, hc15, hlam, hphi, p139_1, u5elo3]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h2, hc25, hlam, hphi, p139_1, u5elo3]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h2, hlam, p139_0]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h112, h2, hc24, hlam, hphi, ht45, p139_1, u5elo3]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h0, hlam, p139_0]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [hlam, p139_0]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h110, hc23, hlam, hphi, ht34, ht45, p139_1, u5elo1]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h0, h2, hlam, p139_1]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h0, h112, h2, hc24, hlam, hphi, ht45, p139_1, u5elo3]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h1, hlam, p139_1]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [hc15, hlam, hphi, p139_1, u5elo2]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [hlam, p139_0]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h110, hlam, p139_1]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h112, hlam, p139_0]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [hc05, hlam, hphi, p139_1, u5elo3]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [hc15, hlam, hphi, p139_1, u5elo3]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [hc25, hlam, hphi, p139_1, u5elo3]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [hlam, p139_0]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h112, hc24, hlam, hphi, ht45, p139_1, u5elo3]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [hc05, hlam, hphi, p139_1, u5elo4]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [hc15, hlam, hphi, p139_1, u5elo4]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [h110, hc23, hlam, hphi, ht34, ht45, p139_1, u5elo4]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [hc35, hlam, hphi, p139_1, u5elo4]
          · have p139_0 := h139c.1
            have p139_1 := h139c.2.1
            have p139_2 := h139c.2.2.1
            have p139_3 := h139c.2.2.2
            linarith only [hlam, p139_0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h165 | h165
    · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
      · rcases m.htr 2 4 5 (by decide) (by decide) with h167 | h167
        · rcases h5bigk with h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hlam, p168_0]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hc15, hlam, hphi, p168_1, u5elo0]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [h1, hlam, p168_0]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hc35, hlam, hphi, p168_1, u5elo0]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [h1, hc45, hlam, hphi, p168_1, u5elo2]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [h0, hlam, p168_0]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hlam, p168_0]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p168_1, u5elo1]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [h0, hc35, hlam, hphi, p168_1, u5elo0]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [h0, h1, hc45, hlam, hphi, p168_1, u5elo2]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hc05, hlam, hphi, p168_1, u5elo2]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hc15, hlam, hphi, p168_1, u5elo2]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hlam, p168_0]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hc35, hlam, hphi, p168_1, u5elo2]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hc45, hlam, hphi, p168_1, u5elo2]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [h165, hlam, p168_1]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hc15, hlam, hphi, p168_1, u5elo3]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [h166, hlam, p168_0]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hlam, p168_0]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [h1, h165, hc45, hlam, hphi, p168_1, u5elo2]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hc05, hlam, hphi, p168_1, u5elo4]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [h167, hc15, hlam, hphi, p168_1, u5elo2]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [h167, hlam, p168_1]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [h167, hc35, hlam, hphi, p168_1, u5elo2]
          · have p168_0 := h168c.1
            have p168_1 := h168c.2.1
            have p168_2 := h168c.2.2.1
            have p168_3 := h168c.2.2.2
            linarith only [hlam, p168_0]
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
            linarith only [h1, hlam, p194_0]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [h1, h167, hc35, hlam, hphi, p194_1, u5elo4]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [h1, h167, hlam, p194_1]
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
            linarith only [h1, hc05, hlam, hphi, p194_1, u5elo1]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [hc35, hlam, hphi, p194_1, u5elo1]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [h0, h167, hc24, hlam, hphi, ht45, p194_1, u5elo0]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [hc05, hlam, hphi, p194_1, u5elo2]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [h167, hc15, hlam, hphi, p194_1, u5elo4]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [hlam, p194_0]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [h167, hc35, hlam, hphi, p194_1, u5elo4]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [h167, hlam, p194_0]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [h165, hlam, p194_1]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [hc15, hlam, hphi, p194_1, u5elo3]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [h166, hlam, p194_0]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [hlam, p194_0]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [h1, h165, h167, hlam, p194_1]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [hc05, hlam, hphi, p194_1, u5elo4]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [hc15, hlam, hphi, p194_1, u5elo4]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [hc25, hlam, hphi, p194_1, u5elo4]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [hc35, hlam, hphi, p194_1, u5elo4]
          · have p194_0 := h194c.1
            have p194_1 := h194c.2.1
            have p194_2 := h194c.2.2.1
            have p194_3 := h194c.2.2.2
            linarith only [hlam, p194_0]
      · linarith only [h1, h165, h166, hlam]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h221 | h221
      · rcases m.htr 2 4 5 (by decide) (by decide) with h222 | h222
        · rcases h5bigk with h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c | h223c
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [hlam, p223_0]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [hc15, hlam, hphi, p223_1, u5elo0]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h1, hlam, p223_0]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h165, hlam, p223_0]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h165, h221, hc45, hlam, hphi, p223_1, u5elo2]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h0, hlam, p223_0]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [hlam, p223_0]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h165, h221, hc03, hlam, hphi, ht34, ht45, p223_1, u5elo1]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h0, h165, hlam, p223_1]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p223_1, u5elo0]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [hc05, hlam, hphi, p223_1, u5elo2]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [hc15, hlam, hphi, p223_1, u5elo2]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [hlam, p223_0]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h165, hc03, hlam, hphi, ht34, ht45, p223_1, u5elo2]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [hc45, hlam, hphi, p223_1, u5elo2]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h1, h221, hc02, hc23, hlam, hphi, p223_1]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h221, hc15, hlam, hphi, p223_1, u5elo2]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h221, hlam, p223_0]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [hlam, p223_0]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h221, hc45, hlam, hphi, p223_1, u5elo2]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p223_1, u5elo4]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h222, hc15, hlam, hphi, p223_1, u5elo2]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h222, hlam, p223_1]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [h222, hc35, hlam, hphi, p223_1, u5elo2]
          · have p223_0 := h223c.1
            have p223_1 := h223c.2.1
            have p223_2 := h223c.2.2.1
            have p223_3 := h223c.2.2.2
            linarith only [hlam, p223_0]
        · rcases h5bigk with h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [hlam, p249_0]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [hc15, hlam, hphi, p249_1, u5elo0]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h1, hlam, p249_0]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h165, hlam, p249_0]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h165, h221, h222, hlam, p249_1]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h0, hlam, p249_0]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [hlam, p249_0]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h165, h221, hc05, hlam, hphi, p249_1, u5elo1]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h0, h165, hc03, hlam, hphi, ht34, ht45, p249_1, u5elo0]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h0, h165, h221, h222, hlam, p249_1]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h222, hc05, hlam, hphi, p249_1, u5elo4]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h222, hc15, hlam, hphi, p249_1, u5elo4]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [hlam, p249_0]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h222, hc35, hlam, hphi, p249_1, u5elo4]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h222, hlam, p249_0]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p249_1, u5elo3]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h221, h222, hc15, hlam, hphi, p249_1, u5elo4]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h221, hlam, p249_0]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [hlam, p249_0]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h221, h222, hlam, p249_1]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p249_1, u5elo4]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [hc15, hlam, hphi, p249_1, u5elo4]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [hc25, hlam, hphi, p249_1, u5elo4]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [h165, hc03, hlam, hphi, ht34, ht45, p249_1, u5elo4]
          · have p249_0 := h249c.1
            have p249_1 := h249c.2.1
            have p249_2 := h249c.2.2.1
            have p249_3 := h249c.2.2.2
            linarith only [hlam, p249_0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h275 | h275
        · rcases h5bigk with h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [hlam, p276_0]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [hc15, hlam, hphi, p276_1, u5elo0]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h1, hlam, p276_0]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h165, hlam, p276_0]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [hc45, hlam, hphi, p276_1, u5elo0]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h0, hlam, p276_0]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [hlam, p276_0]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p276_1, u5elo1]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h0, h221, hc23, hlam, hphi, ht34, ht45, p276_1, u5elo0]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h0, h1, h221, hc45, hlam, hphi, p276_1, u5elo3]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h221, hc05, hlam, hphi, p276_1, u5elo3]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h221, hc15, hlam, hphi, p276_1, u5elo3]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [hlam, p276_0]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h221, hlam, p276_1]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h221, hc45, hlam, hphi, p276_1, u5elo3]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p276_1, u5elo3]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [hc15, hlam, hphi, p276_1, u5elo3]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [hc25, hlam, hphi, p276_1, u5elo3]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [hlam, p276_0]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [hc45, hlam, hphi, p276_1, u5elo3]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p276_1, u5elo4]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h275, hc15, hlam, hphi, p276_1, u5elo2]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h275, hlam, p276_1]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [h221, h275, hlam, p276_1]
          · have p276_0 := h276c.1
            have p276_1 := h276c.2.1
            have p276_2 := h276c.2.2.1
            have p276_3 := h276c.2.2.2
            linarith only [hlam, p276_0]
        · rcases h5bigk with h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [hlam, p302_0]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [hc15, hlam, hphi, p302_1, u5elo0]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h1, hlam, p302_0]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h165, hlam, p302_0]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h1, h275, hlam, p302_1]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h0, hlam, p302_0]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [hlam, p302_0]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h1, hc05, hlam, hphi, p302_1, u5elo1]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h0, hc35, hlam, hphi, p302_1, u5elo0]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h0, h1, h275, hlam, p302_1]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h0, hc15, hlam, hphi, p302_1, u5elo2]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h221, hc15, hlam, hphi, p302_1, u5elo3]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [hlam, p302_0]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h221, hlam, p302_1]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h275, hlam, p302_0]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p302_1, u5elo3]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [hc15, hlam, hphi, p302_1, u5elo3]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [hc25, hlam, hphi, p302_1, u5elo3]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [hlam, p302_0]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h1, h275, hc02, hlam, hphi, ht23, ht34, ht45, p302_1, u5elo3]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p302_1, u5elo4]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [hc15, hlam, hphi, p302_1, u5elo4]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p302_1, u5elo4]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [hc35, hlam, hphi, p302_1, u5elo4]
          · have p302_0 := h302c.1
            have p302_1 := h302c.2.1
            have p302_2 := h302c.2.2.1
            have p302_3 := h302c.2.2.2
            linarith only [hlam, p302_0]

end R2N4
