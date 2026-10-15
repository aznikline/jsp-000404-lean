import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_13_25_L_0_M_LI (m : N7Model)
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5bigk with h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc15, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc25, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc35, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc45, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc05, hlam, hphi, p4_1, u5elo1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h2, h3, hc45, hlam, hphi, p4_1, u5elo1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h3, hc45, hlam, hphi, p4_1, u5elo1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc45, hlam, hphi, p4_1, u5elo1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h0, hlam, p4_1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h0, hc15, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h0, h3, hc45, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc15, hlam, hphi, p4_1, u5elo3]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h2, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc45, hlam, hphi, p4_1, u5elo3]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc05, hlam, hphi, p4_1, u5elo4]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4_1, u3elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h2, h3, hlam, p4_1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h3, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
        · rcases h5bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hlam, p30_0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc15, hlam, hphi, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc25, hlam, hphi, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc35, hlam, hphi, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h3, hc34, hlam, hphi, ht45, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc05, hlam, hphi, p30_1, u5elo1]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hlam, p30_0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h2, h3, hc34, hlam, hphi, ht45, p30_1, u5elo1]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h3, hc34, hlam, hphi, ht45, p30_1, u5elo1]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h3, hc34, hlam, hphi, ht45, p30_1, u5elo1]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h0, hlam, p30_1]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h0, hc15, hlam, hphi, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hlam, p30_0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h0, h3, hc34, hlam, hphi, ht45, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h0, h3, hc34, hlam, hphi, ht45, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h1, hlam, p30_0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc15, hlam, hphi, p30_1, u5elo3]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h2, hlam, p30_0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hlam, p30_0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h3, hlam, p30_1]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc05, hlam, hphi, p30_1, u5elo4]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc15, hlam, hphi, p30_1, u5elo4]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc25, hlam, hphi, p30_1, u5elo4]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc35, hlam, hphi, p30_1, u5elo4]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hlam, p30_0]
      · linarith only [h1, h2, hc23, hlam, hphi, u3elo0]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
      · linarith only [h1, h57, hc03, hlam, hphi, u3elo2]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
        · rcases h5bigk with h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [hlam, p60_0]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [hc15, hlam, hphi, p60_1, u5elo0]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h57, hc23, hlam, hphi, ht34, ht45, p60_1, u5elo0]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h1, hlam, p60_1]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [hc45, hlam, hphi, p60_1, u5elo0]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [hc05, hlam, hphi, p60_1, u5elo1]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [hlam, p60_0]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h57, hc23, hlam, hphi, ht34, ht45, p60_1, u5elo1]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h1, hc03, hlam, hphi, ht34, ht45, p60_1, u5elo1]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [hc45, hlam, hphi, p60_1, u5elo1]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h0, hlam, p60_1]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h0, hc15, hlam, hphi, p60_1, u5elo0]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [hlam, p60_0]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h57, hlam, p60_1]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h0, h1, hc45, hlam, hphi, p60_1, u5elo3]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [hc05, hlam, hphi, p60_1, u5elo3]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [hc15, hlam, hphi, p60_1, u5elo3]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h57, hc23, hlam, hphi, ht34, ht45, p60_1, u5elo3]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [hlam, p60_0]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [hc45, hlam, hphi, p60_1, u5elo3]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h0, h57, hc23, hlam, hphi, ht34, ht45, p60_1, u5elo4]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h59, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p60_1, u3elo3]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h57, h59, hc23, hlam, hphi, p60_1, u3elo3]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [h59, hlam, p60_0]
          · have p60_0 := h60c.1
            have p60_1 := h60c.2.1
            have p60_2 := h60c.2.2.1
            have p60_3 := h60c.2.2.2
            linarith only [hlam, p60_0]
        · rcases h5bigk with h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c | h86c
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [hlam, p86_0]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [hc15, hlam, hphi, p86_1, u5elo0]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h57, hc23, hlam, hphi, ht34, ht45, p86_1, u5elo0]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h1, hlam, p86_1]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h1, h59, hlam, p86_1]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [hc05, hlam, hphi, p86_1, u5elo1]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [hlam, p86_0]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h57, hc23, hlam, hphi, ht34, ht45, p86_1, u5elo1]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [hc35, hlam, hphi, p86_1, u5elo1]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h59, hc34, hlam, hphi, ht45, p86_1, u5elo1]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h0, hlam, p86_1]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h0, hc15, hlam, hphi, p86_1, u5elo0]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [hlam, p86_0]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h57, hlam, p86_1]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h0, h1, h59, hlam, p86_1]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h59, hc05, hlam, hphi, p86_1, u5elo4]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h59, hc15, hlam, hphi, p86_1, u5elo4]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h57, h59, hc23, hlam, hphi, ht34, ht45, p86_1, u5elo4]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [hlam, p86_0]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h59, hlam, p86_1]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h0, h57, hc23, hlam, hphi, ht34, ht45, p86_1, u5elo4]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [hc15, hlam, hphi, p86_1, u5elo4]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [h57, hc23, hlam, hphi, ht34, ht45, p86_1, u5elo4]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [hc35, hlam, hphi, p86_1, u5elo4]
          · have p86_0 := h86c.1
            have p86_1 := h86c.2.1
            have p86_2 := h86c.2.2.1
            have p86_3 := h86c.2.2.2
            linarith only [hlam, p86_0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h112 | h112
    · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
      · rcases m.htr 3 4 5 (by decide) (by decide) with h114 | h114
        · rcases h5bigk with h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [hlam, p115_0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [hc15, hlam, hphi, p115_1, u5elo0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h0, hlam, p115_0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h114, hc45, hlam, hphi, p115_1, u5elo0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p115_1, u5elo2]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [hc05, hlam, hphi, p115_1, u5elo1]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [hlam, p115_0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [hc25, hlam, hphi, p115_1, u5elo1]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h114, hc45, hlam, hphi, p115_1, u5elo1]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [hc45, hlam, hphi, p115_1, u5elo1]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h0, h113, hc02, hlam, hphi, ht23, p115_1, u3elo2]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [hc15, hlam, hphi, p115_1, u5elo2]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [hlam, p115_0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h114, hc45, hlam, hphi, p115_1, u5elo2]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [hc45, hlam, hphi, p115_1, u5elo2]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h112, hlam, p115_0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h112, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p115_1, u3elo0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h113, hlam, p115_0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [hlam, p115_0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h112, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p115_1, u3elo0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [hc05, hlam, hphi, p115_1, u5elo4]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h114, hc15, hlam, hphi, p115_1, u5elo3]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h112, h114, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p115_1, u3elo0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [h114, hlam, p115_0]
          · have p115_0 := h115c.1
            have p115_1 := h115c.2.1
            have p115_2 := h115c.2.2.1
            have p115_3 := h115c.2.2.2
            linarith only [hlam, p115_0]
        · rcases h5bigk with h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hlam, p141_0]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hc15, hlam, hphi, p141_1, u5elo0]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [h0, hlam, p141_0]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hc35, hlam, hphi, p141_1, u5elo0]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p141_1, u5elo2]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hc05, hlam, hphi, p141_1, u5elo1]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hlam, p141_0]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hc25, hlam, hphi, p141_1, u5elo1]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [h114, hc34, hlam, hphi, ht45, p141_1, u5elo1]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [h114, hc34, hlam, hphi, ht45, p141_1, u5elo1]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p141_1, u5elo2]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hc15, hlam, hphi, p141_1, u5elo2]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hlam, p141_0]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [h114, hc34, hlam, hphi, ht45, p141_1, u5elo2]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [h114, hc34, hlam, hphi, ht45, p141_1, u5elo2]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [h112, hlam, p141_0]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hc15, hlam, hphi, p141_1, u5elo3]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [h113, hlam, p141_0]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hlam, p141_0]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [h114, hlam, p141_1]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hc05, hlam, hphi, p141_1, u5elo4]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hc15, hlam, hphi, p141_1, u5elo4]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hc25, hlam, hphi, p141_1, u5elo4]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [h114, hc34, hlam, hphi, ht45, p141_1, u5elo4]
          · have p141_0 := h141c.1
            have p141_1 := h141c.2.1
            have p141_2 := h141c.2.2.1
            have p141_3 := h141c.2.2.2
            linarith only [hlam, p141_0]
      · linarith only [h112, h113, hc23, hlam, hphi, u3elo0]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h168 | h168
      · linarith only [h112, h168, hc03, hlam, hphi, u3elo2]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h170 | h170
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
            linarith only [hc15, hlam, hphi, p171_1, u5elo0]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [h0, hlam, p171_0]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [h112, hlam, p171_1]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [hc45, hlam, hphi, p171_1, u5elo0]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [hc05, hlam, hphi, p171_1, u5elo1]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [hlam, p171_0]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p171_1, u5elo1]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [h0, h168, hc02, hlam, hphi, ht23, ht34, ht45, p171_1, u5elo1]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [hc45, hlam, hphi, p171_1, u5elo1]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [h0, h168, hc02, hlam, hphi, ht23, p171_1, u3elo4]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [h168, hc15, hlam, hphi, p171_1, u5elo3]
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
            linarith only [h168, hc45, hlam, hphi, p171_1, u5elo3]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p171_1, u5elo3]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [hc15, hlam, hphi, p171_1, u5elo3]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [hc25, hlam, hphi, p171_1, u5elo3]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [hlam, p171_0]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [hc45, hlam, hphi, p171_1, u5elo3]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p171_1, u5elo4]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [h170, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p171_1, u3elo3]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [h0, h170, hc02, hlam, hphi, ht23, p171_1, u3elo3]
          · have p171_0 := h171c.1
            have p171_1 := h171c.2.1
            have p171_2 := h171c.2.2.1
            have p171_3 := h171c.2.2.2
            linarith only [h170, hlam, p171_0]
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
            linarith only [hc15, hlam, hphi, p197_1, u5elo0]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [h0, hlam, p197_0]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [h112, hlam, p197_1]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [h0, h168, h170, hlam, p197_1]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [hc05, hlam, hphi, p197_1, u5elo1]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [hlam, p197_0]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [hc25, hlam, hphi, p197_1, u5elo1]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [hc35, hlam, hphi, p197_1, u5elo1]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [h170, hc34, hlam, hphi, ht45, p197_1, u5elo1]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [h0, h168, hc02, hlam, hphi, ht23, p197_1, u3elo4]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [h168, h170, hc15, hlam, hphi, p197_1, u5elo4]
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
            linarith only [h168, h170, hlam, p197_1]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [h0, h170, hc02, hlam, hphi, ht23, ht34, ht45, p197_1, u5elo4]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [h170, hc15, hlam, hphi, p197_1, u5elo4]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [h170, hc25, hlam, hphi, p197_1, u5elo4]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [hlam, p197_0]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [h170, hlam, p197_1]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p197_1, u5elo4]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [hc15, hlam, hphi, p197_1, u5elo4]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p197_1, u5elo4]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [hc35, hlam, hphi, p197_1, u5elo4]
          · have p197_0 := h197c.1
            have p197_1 := h197c.2.1
            have p197_2 := h197c.2.2.1
            have p197_3 := h197c.2.2.2
            linarith only [hlam, p197_0]

theorem r1l7_20_11_13_14_H_R_L_I_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h11, h5, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h14, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h14, h5, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h8, h9, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h18, h3, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                        · linarith only [h21, h5, h8, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                          · linarith only [h0, h23, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h2, h20, h23, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                        · linarith only [h26, h5, h8, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                          · linarith only [h0, h20, h28, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                            · linarith only [h0, h20, h3, h30, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h30, h5, h8, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                    · linarith only [h34, h5, h7, hlam]
                    · linarith only [h33, h34, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                    · linarith only [h0, h3, h33, h37, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
                      · linarith only [h39, h6, h7, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                        · linarith only [h0, h3, h33, h41, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
                          · linarith only [h39, h43, h6, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                          · linarith only [h43, h5, h7, hc45, hlam, hphi, ht34, u3ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                  · linarith only [h47, h5, h6, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                    · linarith only [h0, h3, h4, h47, h49, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                        · linarith only [h0, h3, h47, h52, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h0, h3, h4, h5, h52, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h5, h51, h6, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h5, h56, h6, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                    · linarith only [h0, h3, h4, h56, h58, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                        · linarith only [h0, h3, h56, h61, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h0, h3, h4, h5, h6, h61, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h5, h6, h60, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h65 | h65
              · linarith only [h0, h3, h5, h65, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h67 | h67
                · rcases m.htr 1 3 4 (by decide) (by decide) with h68 | h68
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h69 | h69
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                          · linarith only [h0, h3, h65, h67, h71, h72, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h65, h67, h69, h72, hc45, hlam, hphi, ht34, u3ehi4]
                        · linarith only [h1, h68, h71, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h65, h67, h70, hlam]
                    · linarith only [h68, h69, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                    · linarith only [h0, h3, h4, h68, h78, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h5, h67, h78, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h82 | h82
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h83 | h83
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h86 | h86
                            · linarith only [h1, h81, h86, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h2, h83, h86, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h3, h5, h65, h81, h83, h85, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h5, h81, h84, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                          · linarith only [h0, h3, h83, h91, h92, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h94 | h94
                            · linarith only [h81, h92, h94, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                            · rcases h1bigk with h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                rcases p96_3 (m.d 0 1) (by simp) with h98 | h98
                                · rcases p96_3 (m.d 1 2) (by simp) with h99 | h99
                                  · linarith only [h99, hlam, p96_0]
                                  · rcases p96_3 (m.d 1 3) (by simp) with h101 | h101
                                    · linarith only [h1, h101, hlam]
                                    · linarith only [h101, h5, hlam]
                                · linarith only [h98, hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h82, h94, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p96_1, u3ehi3]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                rcases p96_3 (m.d 0 1) (by simp) with h106 | h106
                                · rcases p96_3 (m.d 1 2) (by simp) with h107 | h107
                                  · linarith only [h0, h107, hlam]
                                  · rcases p96_3 (m.d 1 3) (by simp) with h109 | h109
                                    · linarith only [h1, h109, hlam]
                                    · linarith only [h109, h81, hlam]
                                · linarith only [h106, hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                rcases p96_3 (m.d 0 1) (by simp) with h113 | h113
                                · rcases p96_3 (m.d 1 2) (by simp) with h114 | h114
                                  · linarith only [h0, h114, hlam]
                                  · rcases p96_3 (m.d 1 3) (by simp) with h116 | h116
                                    · linarith only [h1, h116, hlam]
                                    · linarith only [h116, h82, hlam]
                                · linarith only [h113, hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h0, hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h5, hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h65, hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h67, hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h1, hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                rcases p96_3 (m.d 0 1) (by simp) with h126 | h126
                                · rcases p96_3 (m.d 1 2) (by simp) with h127 | h127
                                  · linarith only [h127, h5, hlam]
                                  · rcases p96_3 (m.d 1 3) (by simp) with h129 | h129
                                    · rcases p96_3 (m.d 1 4) (by simp) with h130 | h130
                                      · linarith only [h130, h81, hlam]
                                      · linarith only [h130, h65, hlam]
                                    · linarith only [h129, h5, hlam]
                                · linarith only [h0, h126, hlam]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h0, h3, h5, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p96_1, u3ehi3]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h0, h3, h5, h81, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p96_1, u3ehi3]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h2, hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h65, h92, hc12, hc45, hlam, hphi, ht23, ht34, p96_1]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h81, hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h83, hlam, p96_1]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h0, h3, h5, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p96_1, u3ehi1]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                rcases p96_3 (m.d 0 1) (by simp) with h144 | h144
                                · rcases p96_3 (m.d 1 2) (by simp) with h145 | h145
                                  · linarith only [h145, h67, hlam]
                                  · rcases p96_3 (m.d 1 3) (by simp) with h147 | h147
                                    · rcases p96_3 (m.d 1 4) (by simp) with h148 | h148
                                      · linarith only [h148, h83, hlam]
                                      · linarith only [h148, h65, hlam]
                                    · linarith only [h147, h5, hlam]
                                · linarith only [h0, h144, hlam]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h82, hlam, p96_0]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [h0, h3, h5, h82, hc01, hlam, hphi, ht0b, ht45, ht5b, p96_1, u4ehi1]
                              · have p96_0 := h96c.1
                                have p96_1 := h96c.2.1
                                have p96_2 := h96c.2.2.1
                                have p96_3 := h96c.2.2.2
                                linarith only [hlam, p96_0]
                        · linarith only [h5, h81, h91, hlam]
                    · linarith only [h81, h82, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h158 | h158
                    · linarith only [h0, h158, h3, h4, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h160 | h160
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                        · linarith only [h0, h161, h3, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h163 | h163
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h164 | h164
                            · rcases h1bigk with h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h0, h161, h3, h4, h5, hlam, p165_2]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                rcases p165_3 (m.d 0 1) (by simp) with h168 | h168
                                · rcases p165_3 (m.d 1 2) (by simp) with h169 | h169
                                  · linarith only [h0, h169, hlam]
                                  · rcases p165_3 (m.d 1 3) (by simp) with h171 | h171
                                    · linarith only [h171, hlam, p165_0]
                                    · rcases p165_3 (m.d 1 4) (by simp) with h173 | h173
                                      · linarith only [h173, h2, hlam]
                                      · linarith only [h173, h81, hlam]
                                · linarith only [h168, hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h160, hc01, hlam, hphi, ht0b, ht45, ht5b, p165_1, u4ehi4]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                rcases p165_3 (m.d 0 1) (by simp) with h178 | h178
                                · rcases p165_3 (m.d 1 2) (by simp) with h179 | h179
                                  · linarith only [h0, h179, hlam]
                                  · rcases p165_3 (m.d 1 3) (by simp) with h181 | h181
                                    · linarith only [h1, h181, hlam]
                                    · rcases p165_3 (m.d 1 4) (by simp) with h183 | h183
                                      · linarith only [h183, h2, hlam]
                                      · linarith only [h160, h183, hlam]
                                · linarith only [h178, hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h0, hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h5, hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h65, hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h67, hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h1, hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h158, hc12, hc35, hlam, hphi, ht23, p165_1]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h81, hlam, p165_1]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h158, hlam, p165_1]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h2, hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                rcases p165_3 (m.d 0 1) (by simp) with h198 | h198
                                · rcases p165_3 (m.d 1 2) (by simp) with h199 | h199
                                  · linarith only [h199, h65, hlam]
                                  · rcases p165_3 (m.d 1 3) (by simp) with h201 | h201
                                    · linarith only [h201, h81, hlam]
                                    · linarith only [h201, h5, hlam]
                                · linarith only [h0, h198, hlam]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h161, h3, h4, h65, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p165_1, u3ehi1]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h0, h158, h161, h3, h4, h65, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p165_1, u3ehi1]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h0, h161, h3, h4, h65, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p165_1, u4ehi1]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                rcases p165_3 (m.d 0 1) (by simp) with h209 | h209
                                · rcases p165_3 (m.d 1 2) (by simp) with h210 | h210
                                  · linarith only [h210, h67, hlam]
                                  · rcases p165_3 (m.d 1 3) (by simp) with h212 | h212
                                    · linarith only [h158, h212, hlam]
                                    · linarith only [h212, h5, hlam]
                                · linarith only [h0, h209, hlam]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h0, h161, h163, h3, h4, h67, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p165_1, u3ehi1]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [h160, hlam, p165_0]
                              · have p165_0 := h165c.1
                                have p165_1 := h165c.2.1
                                have p165_2 := h165c.2.2.1
                                have p165_3 := h165c.2.2.2
                                linarith only [hlam, p165_0]
                            · linarith only [h164, h81, hc45, hlam, hphi, ht34, u3ehi1]
                          · linarith only [h160, h163, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h221 | h221
                        · linarith only [h0, h221, h3, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h223 | h223
                          · linarith only [h160, h221, h223, h81, hc34, hlam, hphi, u3ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h225 | h225
                            · linarith only [h0, h223, h225, h3, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                            · linarith only [h225, h81, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc14, hlam, hphi, ht01, u0ehi0]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_11_13_14_H_R_L_R_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h4, h5, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, h4, h5, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h11, h13, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases h3bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h1, h13, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p15_1, u4ehi3]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 3) (by simp) with h18 | h18
                          · rcases p15_3 (m.d 1 3) (by simp) with h19 | h19
                            · linarith only [h1, h19, hlam]
                            · linarith only [h19, h4, hlam]
                          · linarith only [h18, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 3) (by simp) with h23 | h23
                          · rcases p15_3 (m.d 1 3) (by simp) with h24 | h24
                            · linarith only [h1, h24, hlam]
                            · linarith only [h24, h5, hlam]
                          · linarith only [h23, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 3) (by simp) with h28 | h28
                          · rcases p15_3 (m.d 1 3) (by simp) with h29 | h29
                            · linarith only [h1, h29, hlam]
                            · linarith only [h29, h6, hlam]
                          · linarith only [h28, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h1, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 3) (by simp) with h35 | h35
                          · rcases p15_3 (m.d 1 3) (by simp) with h36 | h36
                            · rcases p15_3 (m.d 2 3) (by simp) with h37 | h37
                              · linarith only [h37, h4, hlam]
                              · rcases p15_3 (m.d 3 4) (by simp) with h39 | h39
                                · linarith only [h39, h5, hlam]
                                · linarith only [h39, h7, hlam]
                            · linarith only [h36, h4, hlam]
                          · linarith only [h13, h2, h35, h7, hc45, hlam, hphi, u4ehi0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h1, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h13, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h3, hc23, hlam, hphi, ht01, ht12, p15_1, u0ehi4]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h4, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h7, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h9, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h2, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h5, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h13, hc23, hc45, hlam, hphi, ht34, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h13, hlam, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h3, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h6, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p15_1, u4ehi3]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
              · linarith only [h1, h3, h5, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
              · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                · linarith only [h5, h62, h63, hc23, hlam, hphi, ht12, u1ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h66 | h66
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                      · linarith only [h1, h2, h4, h5, h65, h67, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h5, h62, h66, h67, hc24, hlam, hphi, ht12, u1ehi4]
                    · linarith only [h63, h65, h66, hlam]
                  · linarith only [h1, h2, h5, h62, h65, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
                · linarith only [h5, h72, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h74 | h74
                  · linarith only [h4, h62, h74, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                      · rcases h3bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 3) (by simp) with h80 | h80
                          · rcases p78_3 (m.d 1 3) (by simp) with h81 | h81
                            · linarith only [h1, h81, hlam]
                            · rcases p78_3 (m.d 2 3) (by simp) with h83 | h83
                              · linarith only [h2, h4, h62, h77, h83, hlam]
                              · rcases p78_3 (m.d 3 4) (by simp) with h85 | h85
                                · linarith only [h2, h85, hlam]
                                · linarith only [h5, h85, hlam]
                          · linarith only [h1, h80, hlam]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 3) (by simp) with h89 | h89
                          · rcases p78_3 (m.d 1 3) (by simp) with h90 | h90
                            · linarith only [h1, h90, hlam]
                            · linarith only [h4, h90, hlam]
                          · linarith only [h89, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h1, h62, h77, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi2]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h1, h62, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi2]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h1, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h62, h77, hc23, hc34, hlam, hphi, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h5, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h62, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h2, h62, h77, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h4, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h72, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h74, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h2, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h1, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi2]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 3) (by simp) with h108 | h108
                          · rcases p78_3 (m.d 1 3) (by simp) with h109 | h109
                            · linarith only [h109, h5, hlam]
                            · linarith only [h109, h4, hlam]
                          · linarith only [h108, h2, hlam, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h1, h2, h62, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi2]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h3, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p78_1, u1ehi2]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 3) (by simp) with h117 | h117
                          · rcases p78_3 (m.d 1 3) (by simp) with h118 | h118
                            · linarith only [h118, h62, hlam]
                            · linarith only [h118, h4, hlam]
                          · linarith only [h117, h2, h77, hlam, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h77, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                      · linarith only [h5, h76, h77, hc24, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h125 | h125
                      · linarith only [h1, h125, h2, h76, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h125, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
            · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
              · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h132 | h132
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h133 | h133
                      · linarith only [h1, h128, h133, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · rcases h3bigk with h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h1, h128, hc01, hlam, hphi, ht0b, ht45, ht5b, p135_1, u4ehi3]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h1, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p135_1, u1ehi1]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          rcases p135_3 (m.d 0 3) (by simp) with h139 | h139
                          · rcases p135_3 (m.d 1 3) (by simp) with h140 | h140
                            · linarith only [h1, h140, hlam]
                            · linarith only [h128, h140, hlam]
                          · linarith only [h139, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          rcases p135_3 (m.d 0 3) (by simp) with h144 | h144
                          · rcases p135_3 (m.d 1 3) (by simp) with h145 | h145
                            · linarith only [h1, h145, hlam]
                            · linarith only [h129, h145, hlam]
                          · linarith only [h144, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h1, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h4, hlam, p135_1]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p135_1, u4ehi3]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h1, h133, hc01, hlam, hphi, ht0b, ht45, ht5b, p135_1, u4ehi3]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [hc23, hlam, hphi, ht01, ht12, p135_1, u0ehi2]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [hc23, hlam, hphi, ht12, p135_1, u1ehi2]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          rcases p135_3 (m.d 0 3) (by simp) with h157 | h157
                          · rcases p135_3 (m.d 1 3) (by simp) with h158 | h158
                            · linarith only [h158, h4, hlam]
                            · linarith only [h128, h158, hlam]
                          · linarith only [h157, h2, hlam]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          rcases p135_3 (m.d 0 3) (by simp) with h162 | h162
                          · rcases p135_3 (m.d 1 3) (by simp) with h163 | h163
                            · linarith only [h163, h4, hlam]
                            · linarith only [h129, h163, hlam]
                          · linarith only [h162, h3, hlam]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h2, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h128, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h130, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h133, hlam, p135_1]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h3, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h129, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h131, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h129, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p135_1, u4ehi3]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [hlam, p135_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h177 | h177
                      · linarith only [h132, h177, h2, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases h3bigk with h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h1, h128, hc01, hlam, hphi, ht0b, ht45, ht5b, p179_1, u4ehi3]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h1, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p179_1, u1ehi1]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          rcases p179_3 (m.d 0 3) (by simp) with h183 | h183
                          · rcases p179_3 (m.d 1 3) (by simp) with h184 | h184
                            · linarith only [h1, h184, hlam]
                            · linarith only [h128, h184, hlam]
                          · linarith only [h183, hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          rcases p179_3 (m.d 0 3) (by simp) with h188 | h188
                          · rcases p179_3 (m.d 1 3) (by simp) with h189 | h189
                            · linarith only [h1, h189, hlam]
                            · linarith only [h129, h189, hlam]
                          · linarith only [h188, hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h1, hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h4, hlam, p179_1]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p179_1, u4ehi3]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h1, h177, hc01, hlam, hphi, ht0b, ht45, ht5b, p179_1, u4ehi3]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [hc23, hlam, hphi, ht01, ht12, p179_1, u0ehi2]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [hc23, hlam, hphi, ht12, p179_1, u1ehi2]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          rcases p179_3 (m.d 0 3) (by simp) with h201 | h201
                          · rcases p179_3 (m.d 1 3) (by simp) with h202 | h202
                            · linarith only [h202, h4, hlam]
                            · linarith only [h128, h202, hlam]
                          · linarith only [h2, h201, hlam]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          rcases p179_3 (m.d 0 3) (by simp) with h206 | h206
                          · rcases p179_3 (m.d 1 3) (by simp) with h207 | h207
                            · linarith only [h207, h4, hlam]
                            · linarith only [h129, h207, hlam]
                          · linarith only [h206, h3, hlam]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h2, hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h128, hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h130, hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h177, hlam, p179_1]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h3, hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h129, hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h131, hlam, p179_0]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [h129, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p179_1, u4ehi3]
                        · have p179_0 := h179c.1
                          have p179_1 := h179c.2.1
                          have p179_2 := h179c.2.2.1
                          have p179_3 := h179c.2.2.2
                          linarith only [hlam, p179_0]
                  · linarith only [h1, h129, h131, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                · linarith only [h1, h130, h2, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
              · linarith only [h1, h128, h129, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h224 | h224
              · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
                · linarith only [h128, h225, hc23, hlam, hphi, ht12, u1ehi2]
                · linarith only [h225, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                · linarith only [h128, h228, h4, hc23, hlam, hphi, ht12, u1ehi1]
                · linarith only [h228, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h3, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
      · linarith only [h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

end R2N4
