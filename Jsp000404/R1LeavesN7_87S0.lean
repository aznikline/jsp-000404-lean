import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_R_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h1, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
            · linarith only [h1, h3, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
          · linarith only [h0, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
          · linarith only [h3, h9, hc34, hlam, hphi, u3ehi4]
          · linarith only [h9, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
      · linarith only [h1, h2, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
      · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
        · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
          · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
            · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
              · linarith only [h1, h13, h17, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
              · linarith only [h1, h15, h17, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
            · linarith only [h1, h13, h14, h15, h16, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
          · linarith only [h14, h15, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
          · linarith only [h14, h22, hc34, hlam, hphi, u3ehi4]
          · linarith only [h22, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
        · rcases m.htr 1 3 5 (by decide) (by decide) with h26 | h26
          · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
            · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
              · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
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
                    linarith only [hlam, hphi, ht34, ht45, p30_1, u3ehi4, u5elo0]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [hc45, hlam, hphi, p30_1, u5elo0]
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
                    linarith only [h13, hlam, p30_0]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [h13, hlam, hphi, ht34, ht45, p30_1, u3ehi4, u5elo2]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [h13, hc45, hlam, hphi, p30_1, u5elo2]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [h0, hlam, hphi, ht34, ht45, p30_1, u3ehi4, u5elo2]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [hc15, hlam, hphi, p30_1, u5elo2]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [hlam, p30_0]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [hlam, hphi, ht34, ht45, p30_1, u3ehi4, u5elo2]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [hc45, hlam, hphi, p30_1, u5elo2]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [h0, hlam, p30_0]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [h26, hlam, p30_0]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [h28, hlam, p30_0]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [hlam, p30_0]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [h0, hc45, hlam, hphi, p30_1, u5elo0]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [hc05, hlam, hphi, p30_1, u5elo4]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [h1, h25, h29, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p30_1, u2elo2]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [h1, h25, h29, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p30_1, u2elo2]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [h29, hlam, p30_0]
                  · have p30_0 := h30c.1
                    have p30_1 := h30c.2.1
                    have p30_2 := h30c.2.2.1
                    have p30_3 := h30c.2.2.2
                    linarith only [hlam, p30_0]
                · linarith only [h29, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h0, h1, h28, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
            · linarith only [h1, h26, h27, hc34, hlam, hphi, u3ehi4]
          · linarith only [h25, h26, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h60 | h60
          · linarith only [h25, h60, hc34, hlam, hphi, u3ehi4]
          · linarith only [h60, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
  · linarith only [h0, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem r1l7_10_12_13_25_L_0_L_R_L_0_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
      · linarith only [h2, hlam, hphi, ht23, u2ehi2, u3elo4]
    · linarith only [h1, hlam, hphi, ht23, u2ehi2, u3elo3]
  · linarith only [h0, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_10_12_13_25_L_0_L_R_L_0_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h3, h6, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h0, h3, h5, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · linarith only [h5, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h4, hlam, hphi, ht23, u2ehi2, u3elo4]
        · linarith only [h3, hlam, hphi, ht23, u2ehi2, u3elo3]
      · linarith only [h2, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
    · linarith only [h1, hlam, hphi, ht23, u2ehi1, u3elo2]
  · linarith only [h0, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_10_12_13_25_L_0_L_R_L_0_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
          · linarith only [h4, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
        · linarith only [h2, h3, hc23, hlam, hphi, u3elo1]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
        · linarith only [h2, h8, hc13, hlam, hphi, u3elo2]
        · linarith only [h8, hlam, hphi, ht23, u2ehi2, u3elo3]
    · linarith only [h0, h1, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
    · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
      · linarith only [h0, h12, h13, hlam, hphi, ht23, u2ehi0, u3elo1]
      · linarith only [h0, h12, h13, hlam, hphi, ht23, u2ehi0, u3elo3]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
      · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h17, hlam, hphi, ht23, u2ehi0, u3elo2]
        · linarith only [h17, hlam, hphi, ht23, u2ehi2, u3elo3]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
        · linarith only [h16, h20, hc13, hlam, hphi, u3elo2]
        · linarith only [h20, hlam, hphi, ht23, u2ehi2, u3elo3]

theorem r1l7_10_12_13_25_L_0_L_R_L_I_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h5ehi := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
    · linarith only [h0, h1, hc25, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
    · linarith only [h4, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
      · linarith only [h6, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
        · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
          · linarith only [h8, h9, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · linarith only [h0, h9, hc35, hlam, hphi, ht23, u2ehi0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
          · linarith only [h0, h12, h6, hc23, hlam, hphi, u2ehi0]
          · linarith only [h12, h8, hc35, hlam, hphi, ht23, u2ehi1]

theorem r1l7_10_12_13_25_L_0_L_R_L_R_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
      · linarith only [h1, h2, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
      · linarith only [h5, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
        · linarith only [h0, h7, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
              · linarith only [h1, h11, h9, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                · linarith only [h11, h13, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h15, h7, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h11, h17, h7, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h1, h17, hc45, hlam, hphi, ht34, u3ehi0]
            · linarith only [h0, h10, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
            · linarith only [h21, h9, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h21, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h24 | h24
    · rcases m.htr 0 3 5 (by decide) (by decide) with h25 | h25
      · linarith only [h25, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
      · linarith only [h24, h25, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h28 | h28
      · linarith only [h28, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h30 | h30
        · linarith only [h30, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
          · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
            · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
              · linarith only [h24, h32, h34, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                · linarith only [h28, h34, h36, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                  · linarith only [h33, h38, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · linarith only [h0, h38, hc45, hlam, hphi, ht23, ht34, u2ehi0]
            · linarith only [h32, h33, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
            · linarith only [h32, h42, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
              · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
                  · linarith only [h0, h30, h44, h46, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h42, h46, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h44, h45, hc35, hlam, hphi, u3ehi3]
              · linarith only [h32, h44, hc34, hlam, hphi, ht23, u2ehi1]

theorem r1l7_10_12_13_25_L_0_L_R_L_R_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
          · linarith only [h5, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
      · linarith only [h1, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc23, hlam, hphi, u2ehi4]
    · linarith only [h10, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_10_12_13_25_L_R_L_0_L_0_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
      · linarith only [h1, h2, hc23, hlam, hphi, u3elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]

theorem r1l7_10_12_13_25_L_R_L_0_L_0_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0ehi := hb0.1
  have h0emin := hb0.2.2
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h5, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · linarith only [h0, h10, h11, h5, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h10, h14, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · rcases h0emin with h16 | h16 | h16 | h16 | h16
                          · rcases h5bigk with h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [hlam, p17_0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [hc15, hlam, hphi, p17_1, u5elo0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [hc25, hlam, hphi, p17_1, u5elo0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [hc35, hlam, hphi, p17_1, u5elo0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h10, h8, hc34, hlam, hphi, ht45, p17_1, u5elo0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h1, hlam, p17_0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [hlam, p17_0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h10, h8, hc34, hlam, hphi, ht45, p17_1, u5elo1]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h1, h14, hc34, hlam, hphi, ht45, p17_1, u5elo0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h1, h10, h8, hc34, hlam, hphi, ht45, p17_1, u5elo0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [hlam, hphi, ht01, ht12, p17_1, u0ehi4, u2elo4]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h6, hlam, p17_1]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [hlam, p17_0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h0, h14, h5, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17_1, u2elo0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h10, hlam, p17_1]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h4, hlam, p17_0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [hc15, hlam, hphi, p17_1, u5elo3]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h9, hlam, p17_0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [hlam, p17_0]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h14, hlam, p17_1]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p17_1, u0ehi4]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [hc15, hlam, hphi, p17_1, u5elo4]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h14, h9, hc34, hlam, hphi, ht45, p17_1, u5elo4]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [h14, hc34, hlam, hphi, ht45, p17_1, u5elo4]
                            · have p17_0 := h17c.1
                              have p17_1 := h17c.2.1
                              have p17_2 := h17c.2.2.1
                              have p17_3 := h17c.2.2.2
                              linarith only [hlam, p17_0]
                          · linarith only [h16, hlam, ht01, ht12, u2elo0]
                          · linarith only [h16, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h16, h3, hlam, ht01, ht12, ht23, u3elo0]
                          · linarith only [h0, h14, h16, h5, h9, hc34, hlam, hphi, ht01, ht12, ht45, u2elo0, u5elo0]
                    · linarith only [h4, h9, hc23, hlam, hphi, u3elo0]
                  · linarith only [h3, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h3, h7, hc13, hlam, hphi, u3elo0]
              · linarith only [h5, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · linarith only [h2, h5, hc12, hlam, hphi, u2elo0]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo1]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_10_12_13_25_L_R_L_0_L_0_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
      · linarith only [h1, h2, hc23, hlam, hphi, u3elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]

theorem r1l7_10_12_13_25_L_R_L_0_L_R_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
            · linarith only [h2, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h4, h6, h8, hc34, hlam, hphi, u3ehi2]
              · linarith only [h4, h8, hc45, hlam, hphi, ht34, u3ehi2]
        · linarith only [h1, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
    · linarith only [h0, h1, hc12, hlam, hphi, u2elo0]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]

theorem r1l7_10_12_13_25_L_R_L_0_L_R_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 4 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi4]
      · linarith only [h3, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]

theorem r1l7_10_12_13_25_L_R_L_R_L_0_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h2, h6, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h2, h6, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h7, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
              · linarith only [h6, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h3, h5, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h2, h4, hlam, hphi, ht23, u2ehi2, u3elo3]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · linarith only [h2, hlam, hphi, ht23, u2ehi1, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht23, u2ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h18 | h18
    · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
      · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
        · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
          · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
            · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
              · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h18, h19, h23, h25, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h18, h21, h22, h25, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h18, h21, h22, h24, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h23, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h20, h22, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h19, h21, hlam, hphi, ht23, u2ehi2, u3elo3]
        · linarith only [h0, h20, hc24, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h18, h19, hc23, hlam, hphi, ht01, ht12, u0ehi2]
    · linarith only [h18, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_10_12_13_25_L_R_L_R_L_0_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
            · linarith only [h5, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h2, h4, hlam, hphi, ht23, u2ehi2, u3elo3]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · linarith only [h2, hlam, hphi, ht23, u2ehi1, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht23, u2ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
        · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
          · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
            · linarith only [h0, h12, h14, h15, h16, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
            · linarith only [h16, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h13, h15, hlam, hphi, ht23, u2ehi2, u3elo3]
        · linarith only [h0, h14, hc24, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h12, h13, hc23, hlam, hphi, ht01, ht12, u0ehi2]
    · linarith only [h12, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_10_12_13_25_L_R_L_R_L_R_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
          · linarith only [h2, h4, hc25, hlam, hphi, u2ehi2]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
        · linarith only [h2, h8, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
          · linarith only [h10, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
            · linarith only [h1, h12, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                · linarith only [h12, h15, h2, hc23, hlam, hphi, u2ehi1]
                · linarith only [h14, h15, hc35, hlam, hphi, u3ehi3]
              · linarith only [h14, h2, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
      · linarith only [h0, h1, h19, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
      · linarith only [h0, h1, h19, hc23, hlam, hphi, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h22 | h22
    · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
        · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
          · rcases m.htr 1 3 5 (by decide) (by decide) with h26 | h26
            · linarith only [h22, h26, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
              · linarith only [h0, h22, h23, h28, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                · linarith only [h23, h26, h30, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h32 | h32
                  · linarith only [h24, h32, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                    · linarith only [h32, h34, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h28, h34, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h0, h22, h23, h25, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h22, h23, h24, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h22, h23, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
      · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
        · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
          · rcases m.htr 1 3 5 (by decide) (by decide) with h43 | h43
            · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
              · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                · linarith only [h40, h45, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · linarith only [h40, h43, h44, h45, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                · linarith only [h44, h48, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                  · linarith only [h41, h50, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                    · linarith only [h50, h52, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h44, h52, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h22, h43, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
          · linarith only [h0, h42, hc25, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h22, h40, h41, hc24, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h40, hc23, hlam, hphi, ht01, ht12, u0ehi0]

theorem r1l7_10_12_13_25_L_R_L_R_L_R_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · rcases h5bigk with h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc15, hlam, hphi, p3_1, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht23, ht34, ht45, p3_1, u2ehi4, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc35, hlam, hphi, p3_1, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc45, hlam, hphi, p3_1, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht23, ht34, ht45, p3_1, u2ehi4, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, hphi, ht34, ht45, p3_1, u3ehi4, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc45, hlam, hphi, p3_1, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc25, hlam, hphi, ht01, ht12, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, h1, hlam, hphi, ht34, ht45, p3_1, u3ehi4, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, h1, hc45, hlam, hphi, p3_1, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, hphi, ht23, ht34, ht45, p3_1, u2ehi4, u5elo3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht23, ht34, ht45, p3_1, u2ehi4, u5elo3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc45, hlam, hphi, p3_1, u5elo3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, h2, hlam, hphi, ht23, ht34, ht45, p3_1, u2ehi4, u5elo3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, hphi, ht23, ht34, ht45, p3_1, u2ehi4, u5elo3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
      · linarith only [h2, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo1]

theorem r1l7_10_12_13_25_L_R_L_R_L_R_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · linarith only [h2, h5, h7, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                · linarith only [h7, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h6, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
            · linarith only [h0, h4, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
            · linarith only [h12, h2, h4, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
              · linarith only [h14, h2, h4, hc34, hlam, hphi, u3ehi4]
              · linarith only [h14, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
        · linarith only [h18, h2, hc23, hlam, hphi, u2ehi4]
        · linarith only [h18, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
    · linarith only [h0, h1, hlam, hphi, ht34, ht45, u3ehi0, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h22 | h22
    · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
      · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
        · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
          · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
            · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
              · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                · linarith only [h23, h26, h28, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                · linarith only [h28, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h27, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
              · linarith only [h26, h32, hc34, hlam, hphi, u3ehi4]
              · linarith only [h32, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
          · linarith only [h0, h22, h24, h25, hc34, hlam, hphi, ht23, u2ehi4]
        · linarith only [h24, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
        · linarith only [h23, h37, hc23, hlam, hphi, u2ehi4]
        · linarith only [h37, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
    · linarith only [h22, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo1]

theorem r1l7_10_12_23_L_0_L_0_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_L m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h2, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · linarith only [h3, hc23, hlam, hphi, u3elo3]
      · linarith only [h2, hc12, hlam, hphi, ht23, u3elo2]
    · linarith only [h1, hc01, hlam, hphi, ht12, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h8 | h8
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
      · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
        · linarith only [h0, h10, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
        · linarith only [h10, hc23, hlam, hphi, u3elo3]
      · linarith only [h0, h9, hc01, hlam, hphi, ht12, u2elo2]
    · linarith only [h8, hc01, hlam, hphi, ht12, ht23, u3elo1]

theorem r1l7_10_12_23_L_0_L_R_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h3, h6, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h0, h3, h5, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
              · linarith only [h5, h9, hlam, hphi, ht23, u2ehi3, u3elo3]
              · rcases h3bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hc13, hlam, hphi, p11_1, u3elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hc23, hlam, hphi, p11_1, u3elo0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  rcases p11_3 (m.d 0 3) (by simp) with h15 | h15
                  · rcases p11_3 (m.d 1 3) (by simp) with h16 | h16
                    · rcases p11_3 (m.d 2 3) (by simp) with h17 | h17
                      · linarith only [h0, h17, hlam]
                      · linarith only [h17, h3, hlam]
                    · linarith only [h1, h16, h3, hlam]
                  · linarith only [h15, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  rcases p11_3 (m.d 0 3) (by simp) with h22 | h22
                  · rcases p11_3 (m.d 1 3) (by simp) with h23 | h23
                    · rcases p11_3 (m.d 2 3) (by simp) with h24 | h24
                      · linarith only [h0, h24, hlam]
                      · linarith only [h24, h4, hlam]
                    · linarith only [h23, hc13, hlam, hphi, p11_1, u3elo0]
                  · linarith only [h22, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hc03, hlam, hphi, p11_1, u3elo1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h4, h5, hlam, hphi, ht23, p11_1, u2ehi3, u3elo1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  rcases p11_3 (m.d 0 3) (by simp) with h32 | h32
                  · rcases p11_3 (m.d 1 3) (by simp) with h33 | h33
                    · rcases p11_3 (m.d 2 3) (by simp) with h34 | h34
                      · linarith only [h1, h34, hlam]
                      · linarith only [h3, h34, hlam]
                    · linarith only [h33, hlam, p11_0]
                  · linarith only [h0, h3, h32, hlam]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  rcases p11_3 (m.d 0 3) (by simp) with h39 | h39
                  · rcases p11_3 (m.d 1 3) (by simp) with h40 | h40
                    · rcases p11_3 (m.d 2 3) (by simp) with h41 | h41
                      · linarith only [h1, h41, hlam]
                      · linarith only [h4, h41, hlam]
                    · linarith only [h40, hlam, p11_0]
                  · linarith only [h39, hc03, hlam, hphi, p11_1, u3elo1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h0, hlam, p11_0]
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
                  linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1, u0elo1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h0, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1, u0elo1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h0, h4, h5, hlam, hphi, ht23, p11_1, u2ehi3, u3elo3]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h0, h4, h9, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p11_1, u0elo1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h3, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h9, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h0, h4, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h1, h4, hlam, p11_1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h4, hlam, p11_0]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [h0, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1, u0elo1]
                · have p11_0 := h11c.1
                  have p11_1 := h11c.2.1
                  have p11_2 := h11c.2.2.1
                  have p11_3 := h11c.2.2.2
                  linarith only [hlam, p11_0]
          · linarith only [h4, hlam, hphi, ht23, u2ehi2, u3elo4]
        · linarith only [h3, hlam, hphi, ht23, u2ehi2, u3elo3]
      · linarith only [h1, h2, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h1, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
  · linarith only [h0, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_10_12_23_L_R_L_0_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi4]
            · linarith only [h0, h1, h5, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
          · linarith only [h0, h1, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
          · linarith only [h3, h9, hc34, hlam, hphi, u3ehi4]
          · linarith only [h0, h1, h9, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
      · linarith only [h0, h2, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
        · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
          · linarith only [h1, h13, h15, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
          · linarith only [h14, h15, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
          · linarith only [h14, h18, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
            · linarith only [h0, h18, h20, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
              · rcases h3bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [hlam, p23_0]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h1, h13, h22, hc34, hlam, hphi, p23_1, u3ehi2]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h1, h22, hc34, hlam, hphi, p23_1, u3ehi2]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h1, h22, hlam, p23_1]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h1, hlam, p23_0]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [hc13, hlam, hphi, ht01, p23_1, u0ehi2]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [hlam, p23_0]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p23_1, u2elo1, u3ehi2]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h14, hlam, p23_0]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h18, hlam, p23_0]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h0, hlam, p23_0]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h13, hlam, p23_0]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [hlam, p23_0]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h18, h22, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p23_1, u2elo2, u3ehi1]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h20, hlam, p23_0]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p23_1, u0ehi2]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [hc34, hlam, hphi, p23_1, u3ehi1]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [hc34, hlam, hphi, p23_1, u3ehi2]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [hlam, p23_0]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h1, hc34, hlam, hphi, ht01, ht12, ht23, p23_1, u0ehi2]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p23_1, u0ehi2]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h13, hc35, hlam, hphi, p23_1, u3ehi2]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [hc35, hlam, hphi, p23_1, u3ehi2]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [h22, hlam, p23_0]
                · have p23_0 := h23c.1
                  have p23_1 := h23c.2.1
                  have p23_2 := h23c.2.2.1
                  have p23_3 := h23c.2.2.2
                  linarith only [hlam, p23_0]
              · linarith only [h13, h14, h22, hc45, hlam, hphi, ht34, u3ehi2]
      · linarith only [h0, h13, hc12, hlam, hphi, u2elo0]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]

theorem r1l7_10_12_23_L_R_L_R_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
        · linarith only [h4, hc34, hlam, hphi, u3ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
      · linarith only [h0, h1, h7, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
      · linarith only [h0, h1, h7, hc23, hlam, hphi, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
      · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
        · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
          · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
            · linarith only [h12, h15, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h15, hc34, hlam, hphi, u3ehi2]
          · linarith only [h14, hc35, hlam, hphi, u3ehi1]
        · linarith only [h10, h13, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
      · linarith only [h0, h12, hc23, hlam, hphi, ht01, ht12, u0ehi0]

theorem r1l7_10_12_25_L_0_L_0_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · linarith only [h0, h1, h3, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h6 | h6
    · linarith only [h6, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
      · linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi2]
      · linarith only [h0, h8, hc01, hlam, hphi, ht12, u2elo4]

theorem r1l7_10_12_25_L_0_L_0_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi7]
            · linarith only [h3, h5, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
            · linarith only [h4, h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
            · linarith only [h3, h8, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
            · linarith only [h12, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
            · linarith only [h11, h12, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
            · linarith only [h11, h15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
              · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                · linarith only [h1, h18, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                · linarith only [h17, h18, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                · linarith only [h1, h21, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                  · linarith only [h17, h23, h3, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                    · linarith only [h21, h25, h3, hc12, hlam, hphi, u2elo2]
                    · linarith only [h25, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h29 | h29
      · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
        · linarith only [h0, h1, h30, hlam]
        · linarith only [h0, h1, h30, hc12, hlam, hphi, u2elo2]
      · linarith only [h0, h29, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h34 | h34
    · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
      · linarith only [h0, h35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
      · linarith only [h34, h35, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h38 | h38
      · linarith only [h0, h38, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi6]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
        · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
          · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
            · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
              · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
                · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h46 | h46
                    · linarith only [h40, h46, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                    · linarith only [h45, h46, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                    · linarith only [h40, h49, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
                      · linarith only [h41, h51, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h53 | h53
                        · linarith only [h40, h43, h51, h53, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h45, h53, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h34, h44, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h57 | h57
                · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                  · linarith only [h43, h57, h58, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi8]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                    · linarith only [h40, h60, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                    · linarith only [h43, h57, h60, hc23, hc34, hlam, hphi]
                · linarith only [h34, h57, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h41, h42, hc24, hlam, hphi, ht45, u5elo2]
          · linarith only [h34, h40, h41, hc01, hlam, hphi, ht12, u2elo3]
        · linarith only [h0, h40, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_10_12_25_L_0_L_R_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc24 := m.hcor 2 4 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi9]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
      · linarith only [h1, h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h8 | h8
    · linarith only [h0, h8, hc24, hlam, hphi, u2ehi4]
    · linarith only [h8, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_10_12_25_L_R_L_0_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]

theorem r1l7_10_12_25_L_R_L_0_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h5, h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                  · linarith only [h7, h8, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                  · linarith only [h1, h11, h3, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi8]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                    · linarith only [h1, h13, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi9]
                    · linarith only [h13, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h2, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h1, h5, hc12, hlam, hphi, u2elo0]
          · linarith only [h3, h4, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
            · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
              · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                · linarith only [h19, h20, h22, h3, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                  · linarith only [h20, h24, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                  · linarith only [h19, h24, h3, hc23, hc34, hlam, hphi]
              · linarith only [h2, h21, hc12, hlam, hphi, u2elo0]
            · linarith only [h1, h20, hc12, hlam, hphi, u2elo0]
          · linarith only [h19, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_10_12_25_L_R_L_I_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
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
            linarith only [hc15, hlam, hphi, ht01, p4_1, u0ehi4]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h3, hc35, hlam, hphi, p4_1, u5elo1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc35, hlam, hphi, p4_1, u5elo1]
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
            linarith only [hc15, hlam, hphi, p4_1, u5elo2]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h0, hc35, hlam, hphi, p4_1, u5elo0]
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
            linarith only [h3, hlam, p4_0]
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
            linarith only [h2, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc15, hlam, hphi, p4_1, u5elo4]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h2, hc25, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h2, hc35, hlam, hphi, p4_1, u5elo0]
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
            linarith only [h3, hc23, hlam, hphi, ht34, ht45, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h3, hc23, hlam, hphi, ht34, ht45, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc45, hlam, hphi, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc15, hlam, hphi, ht01, p30_1, u0ehi4]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hlam, p30_0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h3, hc23, hlam, hphi, ht34, ht45, p30_1, u5elo1]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h3, hc23, hlam, hphi, ht34, ht45, p30_1, u5elo1]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc45, hlam, hphi, p30_1, u5elo1]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h0, hlam, p30_1]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc15, hlam, hphi, p30_1, u5elo2]
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
            linarith only [h1, h3, hc45, hlam, hphi, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h1, hlam, p30_0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h1, hc15, hlam, hphi, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h1, hc25, hlam, hphi, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hlam, p30_0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h1, hc45, hlam, hphi, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h2, hlam, p30_0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hc15, hlam, hphi, p30_1, u5elo4]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h2, h3, hc23, hlam, hphi, ht34, ht45, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [h2, hc35, hlam, hphi, p30_1, u5elo0]
          · have p30_0 := h30c.1
            have p30_1 := h30c.2.1
            have p30_2 := h30c.2.2.1
            have p30_3 := h30c.2.2.2
            linarith only [hlam, p30_0]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo2]

end R2N4
