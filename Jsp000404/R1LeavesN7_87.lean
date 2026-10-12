import Jsp000404.S7Defs

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

theorem r1l7_10_12_25_L_R_L_R_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
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
          linarith only [hc15, hlam, hphi, ht01, p3_1, u0ehi4]
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
          linarith only [hc35, hlam, hphi, p3_1, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc45, hlam, hphi, p3_1, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc25, hlam, hphi, ht01, ht12, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc35, hlam, hphi, p3_1, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc45, hlam, hphi, p3_1, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc15, hlam, hphi, p3_1, u5elo3]
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
          linarith only [h1, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, h2, hc35, hlam, hphi, p3_1, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
      · linarith only [h2, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
      · linarith only [h0, h1, h30, hlam]
      · linarith only [h30, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
  · linarith only [h0, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]

theorem r1l7_10_13_25_L_0_L_R_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0elo := hb0.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
    · linarith only [h0, h1, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
    · linarith only [h4, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
      · linarith only [h6, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
        · linarith only [h0, h6, h8, hc34, hlam, hphi, u3ehi0]
        · linarith only [h0, h8, hc45, hlam, hphi, ht34, u3ehi0]

theorem r1l7_10_13_25_L_0_L_R_M_LR (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi9]
      · linarith only [h2, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
    · linarith only [h1, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
    · linarith only [h0, h6, hc34, hlam, hphi, u3ehi4]
    · linarith only [h6, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem r1l7_10_13_25_L_R_L_0_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi3]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]

theorem r1l7_10_23_L_0_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig2_7_H_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h3ehi := hb3.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
  · linarith only [h0, hc34, hlam, hphi, u3ehi0]

theorem r1l7_10_23_L_R_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig2_7_H_L m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.1
  have h3elo := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo0]

theorem r1l7_10_25_L_0_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem r1l7_10_25_L_R_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem r1l7_11_12_14_25_L_0_L_0_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi2]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
      · linarith only [h5, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
        · linarith only [h0, h1, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
          · linarith only [h0, h1, h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
            · linarith only [h0, h1, h11, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
              · linarith only [h13, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
              · linarith only [h0, h1, h13, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
    · linarith only [h0, h16, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
      · linarith only [h0, h18, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
        · linarith only [h20, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
          · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
            · linarith only [h23, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
              · linarith only [h22, h23, h25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                · linarith only [h16, h22, h23, h25, h27, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h22, h23, h27, hc45, hlam, hphi, u4ehi3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
            · linarith only [h30, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h32 | h32
              · linarith only [h32, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                · linarith only [h0, h22, h32, h34, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h22, h34, hc12, hc45, hlam, hphi, ht23, ht34]

theorem r1l7_11_12_14_25_L_0_L_0_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
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
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
            · linarith only [h4, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi7]
            · linarith only [h3, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
          · linarith only [h3, h9, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
            · linarith only [h11, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
              · linarith only [h1, h13, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
                · linarith only [h1, h15, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h15, h17, h3, hc12, hlam, hphi, u2elo2]
                  · linarith only [h17, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h21 | h21
      · linarith only [h1, h21, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi6]
      · linarith only [h0, h21, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h24 | h24
    · rcases m.htr 0 1 5 (by decide) (by decide) with h25 | h25
      · linarith only [h0, h25, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi6]
      · linarith only [h24, h25, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h28 | h28
      · linarith only [h24, h28, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi6]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
        · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
          · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
            · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
              · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h30, h35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                    · linarith only [h31, h37, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
                    · linarith only [h37, hlam, hphi, ht45, u4ehi2, u5elo4]
                · linarith only [h33, h34, hlam, hphi, ht45, u4ehi3, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h41 | h41
                · rcases m.htr 2 3 5 (by decide) (by decide) with h42 | h42
                  · linarith only [h30, h42, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
                  · linarith only [h33, h41, h42, hc23, hc34, hlam, hphi]
                · linarith only [h24, h41, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h32, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h24, h30, h31, hc01, hlam, hphi, ht12, u2elo3]
        · linarith only [h0, h30, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_11_12_14_25_L_0_L_R_L_0_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc25 := m.hcor 2 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
      · linarith only [h2, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
    · linarith only [h0, h1, hc25, hlam, hphi, u2ehi3]
  · linarith only [h0, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]

theorem r1l7_11_12_14_25_L_0_L_R_L_0_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h1, h3, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
            · linarith only [h0, h5, hc34, hlam, hphi, u4elo0]
          · linarith only [h0, h4, hc24, hlam, hphi, u4elo0]
        · linarith only [h3, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
      · linarith only [h2, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
      · linarith only [h1, h11, hc23, hlam, hphi, u2ehi3]
      · linarith only [h11, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
    · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
      · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
        · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
          · linarith only [h0, h14, h16, h17, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · linarith only [h17, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
        · linarith only [h16, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
      · linarith only [h15, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
      · linarith only [h14, h22, hc23, hlam, hphi, u2ehi3]
      · linarith only [h22, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]

theorem r1l7_11_12_14_25_L_0_L_R_L_0_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.2.1
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h2, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
        · linarith only [h3, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
      · linarith only [h2, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
    · linarith only [h0, h1, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
    · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
      · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
        · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
          · linarith only [h11, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi9]
          · linarith only [h10, h11, hc34, hlam, hphi, u4elo2]
        · linarith only [h10, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
      · linarith only [h9, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
    · linarith only [h0, h8, hlam, hphi, ht23, ht34, u2ehi1, u4elo3]

theorem r1l7_11_12_14_25_L_0_L_R_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
          · linarith only [h2, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
            · linarith only [h0, h7, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
            · linarith only [h2, h3, h7, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
        · linarith only [h10, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
          · linarith only [h1, h12, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
            · linarith only [h0, h14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
              · linarith only [h1, h12, h16, h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                · linarith only [h1, h12, h14, h18, hc34, hlam, hphi, ht23, u2ehi2]
                · linarith only [h0, h18, h2, hc45, hlam, hphi, ht23, ht34, u2ehi2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
    · linarith only [h0, h22, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
      · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
        · linarith only [h25, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h27 | h27
          · linarith only [h24, h25, h27, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
            · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
              · linarith only [h22, h27, h30, hc24, hlam, hphi, u2ehi1]
              · linarith only [h22, h30, hc45, hlam, hphi, ht23, ht34, u2ehi1]
            · linarith only [h24, h25, h29, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
        · linarith only [h34, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
          · linarith only [h36, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
            · linarith only [h0, h24, h38, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h38, hc34, hlam, hphi, ht23, u2ehi1]

theorem r1l7_11_12_14_25_L_0_L_R_L_R_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
      · linarith only [h0, h1, h2, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
      · linarith only [h0, h1, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
        · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
          · linarith only [h0, h7, h8, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
          · linarith only [h1, h8, hc13, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h7, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
    · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
      · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
        · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
          · linarith only [h12, h15, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi4]
          · linarith only [h15, hlam, hphi, ht45, u4ehi3, u5elo4]
        · linarith only [h0, h12, h14, hlam, hphi, ht45, u4ehi1, u5elo3]
      · linarith only [h0, h12, h13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi1]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
      · linarith only [h0, h12, h20, hc23, hlam, hphi, u2ehi1]
      · linarith only [h0, h20, hc34, hlam, hphi, ht23, u2ehi1]

theorem r1l7_11_12_14_25_L_0_L_R_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
      · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
    · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
      · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
        · linarith only [h6, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
        · linarith only [h8, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
      · linarith only [h0, h7, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
      · linarith only [h12, h6, hc23, hlam, hphi, u2ehi4]
      · linarith only [h0, h12, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem r1l7_11_12_14_25_L_I_L_0_L_0_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
            · linarith only [h2, h3, h4, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h2, h3, h4, h6, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h3, h4, h8, hc34, hlam, hphi, u4elo4]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
          · linarith only [h11, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
            · linarith only [h1, h13, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h13, h15, h3, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h15, h3, hc23, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
        · linarith only [h0, h18, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
          · linarith only [h1, h18, h2, h20, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
            · linarith only [h1, h2, h22, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
            · linarith only [h1, h18, h2, h22, hc23, hlam, hphi, ht34, u4elo4]
    · linarith only [h0, h1, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
    · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
      · linarith only [h0, h27, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
        · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
          · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
            · linarith only [h26, h27, h30, h31, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
            · linarith only [h26, h27, h29, h31, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h34 | h34
            · linarith only [h26, h34, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
            · linarith only [h0, h26, h30, h34, hc24, hlam, hphi, u4elo4]
        · linarith only [h0, h26, h29, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
      · linarith only [h26, h38, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
        · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
          · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
            · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
              · linarith only [h40, h43, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
              · linarith only [h42, h43, hc34, hlam, hphi, u4elo2]
            · linarith only [h26, h42, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
            · linarith only [h40, h41, h47, hlam]
            · linarith only [h26, h47, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · linarith only [h0, h40, hc12, hlam, hphi, ht23, ht34, u4elo3]

theorem r1l7_11_12_14_25_L_R_L_0_L_0_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc24 := m.hcor 2 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h3, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
            · linarith only [h2, h6, hc24, hlam, hphi, u4elo1]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
          · linarith only [h0, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
            · linarith only [h1, h11, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
            · linarith only [h11, h2, hc24, hlam, hphi, u4elo1]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
    · linarith only [h1, hlam, hphi, ht12, u1ehi1, u2elo3]
  · linarith only [h0, hlam, hphi, ht12, u1ehi1, u2elo2]

theorem r1l7_11_12_14_25_L_R_L_0_L_0_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc05 := m.hcor 0 5 (by decide)
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
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h4, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · linarith only [h11, h7, hc34, hlam, hphi, u4elo1]
                      · linarith only [h10, h7, hc24, hlam, hphi, u4elo1]
                    · linarith only [h8, h9, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h0, h16, h4, h5, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                        · rcases h5bigk with h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hc15, hlam, hphi, p20_1, u5elo0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hc25, hlam, hphi, p20_1, u5elo0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h16, hc23, hlam, hphi, ht34, ht45, p20_1, u5elo0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hc45, hlam, hphi, p20_1, u5elo0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h1, hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h16, hc23, hlam, hphi, ht34, ht45, p20_1, u5elo1]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h1, h16, hc23, hlam, hphi, ht34, ht45, p20_1, u5elo0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h1, hc45, hlam, hphi, p20_1, u5elo0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h2, hlam, p20_1]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hlam, hphi, ht12, p20_1, u1ehi4, u2elo4]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h16, hlam, p20_1]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hc45, hlam, hphi, p20_1, u5elo2]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h3, hlam, p20_1]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h6, hlam, p20_1]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hc25, hlam, hphi, p20_1, u5elo3]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h0, h19, h4, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p20_1, u2elo0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hc05, hlam, hphi, p20_1, u5elo4]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h7, hlam, p20_1]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h18, hlam, p20_1]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h19, hlam, p20_1]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hlam, p20_0]
                        · linarith only [h18, h19, h8, hlam]
                      · linarith only [h18, h7, hc24, hlam, hphi, u4elo1]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h5, h6, hc34, hlam, hphi, ht45, u5elo3]
            · linarith only [h5, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
          · linarith only [h4, hlam, hphi, ht12, u1ehi1, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
          · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
            · rcases m.htr 1 3 5 (by decide) (by decide) with h54 | h54
              · linarith only [h1, h3, h52, h54, hlam, hphi, ht12, u1ehi4, u2elo1]
              · linarith only [h53, h54, hc34, hlam, hphi, ht45, u5elo3]
            · linarith only [h53, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
          · linarith only [h52, hlam, hphi, ht12, u1ehi1, u2elo2]
      · linarith only [h0, h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
  · linarith only [h0, hlam, hphi, ht12, u1ehi0, u2elo1]

theorem r1l7_11_12_14_25_L_R_L_0_L_0_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc24 := m.hcor 2 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.2.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h3, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
          · linarith only [h2, h4, hc24, hlam, hphi, u4elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
          · linarith only [h1, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
          · linarith only [h2, h7, hc24, hlam, hphi, u4elo1]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
    · linarith only [h1, hlam, hphi, ht12, u1ehi1, u2elo3]
  · linarith only [h0, hlam, hphi, ht12, u1ehi1, u2elo2]

theorem r1l7_11_12_14_25_L_R_L_0_L_I_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
          · linarith only [h3, h4, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
          · linarith only [h0, h1, h3, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
            · linarith only [h0, h1, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
            · linarith only [h3, h9, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
      · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
        · linarith only [h1, h13, h14, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi8]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
          · linarith only [h0, h16, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
          · linarith only [h1, h13, h16, hc23, hc34, hlam, hphi]
      · linarith only [h13, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
  · linarith only [h0, hlam, hphi, ht12, u1ehi1, u2elo2]

theorem r1l7_11_12_14_25_L_R_L_0_L_R_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5emax := hb5.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h2, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
            · linarith only [h2, h4, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi3]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
            · linarith only [h2, h8, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
            · rcases h5emax with h10 | h10 | h10 | h10 | h10
              · linarith only [h0, h10, hlam, ht12, ht23, ht34, ht45, u1ehi4]
              · linarith only [h10, hlam, ht12, ht23, ht34, ht45, u1ehi4]
              · linarith only [h10, h4, hlam, ht45, u4ehi2]
              · linarith only [h10, h8, hlam, ht45, u4ehi3]
              · linarith only [h10, h2, h4, hlam, ht45, u4ehi3]
        · linarith only [h1, h2, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
        · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
          · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
            · rcases h5emax with h20 | h20 | h20 | h20 | h20
              · linarith only [h0, h20, hlam, ht12, ht23, ht34, ht45, u1ehi4]
              · linarith only [h20, hlam, ht12, ht23, ht34, ht45, u1ehi4]
              · linarith only [h17, h19, h20, hlam, ht45, u4ehi4]
              · linarith only [h19, h20, hlam, ht45, u4ehi4]
              · linarith only [h20, hlam, ht45, u4ehi4]
            · linarith only [h1, h18, h19, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
          · linarith only [h17, h18, h2, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
          · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
            · rcases h5emax with h30 | h30 | h30 | h30 | h30
              · linarith only [h0, h30, hlam, ht12, ht23, ht34, ht45, u1ehi4]
              · linarith only [h30, hlam, ht12, ht23, ht34, ht45, u1ehi4]
              · linarith only [h28, h30, hlam, ht45, u4ehi4]
              · linarith only [h17, h30, hc23, hlam, ht34, ht45]
              · linarith only [h30, hlam, ht45, u4ehi4]
            · linarith only [h2, h28, h29, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
            · rcases h5emax with h38 | h38 | h38 | h38 | h38
              · linarith only [h0, h38, hlam, ht12, ht23, ht34, ht45, u1ehi4]
              · linarith only [h38, hlam, ht12, ht23, ht34, ht45, u1ehi4]
              · linarith only [h28, h38, hlam, ht45, u4ehi2]
              · linarith only [h37, h38, hlam, ht45, u4ehi4]
              · linarith only [h38, hlam, ht45, u4ehi4]
            · rcases h5emax with h44 | h44 | h44 | h44 | h44
              · linarith only [h0, h44, hlam, ht12, ht23, ht34, ht45, u1ehi4]
              · linarith only [h44, hlam, ht12, ht23, ht34, ht45, u1ehi4]
              · linarith only [h28, h44, hlam, ht45, u4ehi2]
              · linarith only [h17, h28, h44, hlam, ht45, u4ehi2]
              · linarith only [h2, h37, h44, hc23, hlam, ht34, ht45]
    · linarith only [h1, hlam, hphi, ht12, u1ehi1, u2elo4]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
    · linarith only [h0, h51, hlam, hphi, ht12, u1ehi0, u2elo1]
    · linarith only [h51, hlam, hphi, ht12, u1ehi1, u2elo4]

theorem r1l7_11_12_14_25_L_R_L_0_L_R_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 4 5 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
    · linarith only [h1, hlam, hphi, ht45, u4ehi2, u5elo4]
  · linarith only [h0, hlam, hphi, ht12, u1ehi1, u2elo3]

theorem r1l7_11_12_14_25_L_R_L_0_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · linarith only [h1, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
        · linarith only [h3, hlam, hphi, ht45, u4ehi2, u5elo4]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
    · linarith only [h1, hlam, hphi, ht12, u1ehi1, u2elo3]
  · linarith only [h0, hlam, hphi, ht12, u1ehi1, u2elo2]

theorem r1l7_11_12_14_25_L_R_L_R_L_0_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.2.1
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
          · linarith only [h1, h3, h4, hc34, hlam, hphi, u4elo1]
        · linarith only [h3, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
      · linarith only [h2, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
    · linarith only [h1, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc23, hlam, hphi, u2ehi3]
    · linarith only [h10, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]

theorem r1l7_11_12_14_25_L_R_L_R_L_R_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 3 4 5 (by decide) (by decide) with h1 | h1
    · rcases h5emax with h2 | h2 | h2 | h2 | h2
      · linarith only [h0, h2, hlam, ht12, ht23, ht34, ht45, u1ehi4]
      · linarith only [h2, hlam, ht12, ht23, ht34, ht45, u1ehi4]
      · linarith only [h2, hlam, ht23, ht34, ht45, u2ehi4]
      · linarith only [h1, h2, hlam, ht45, u4ehi4]
      · linarith only [h2, hlam, ht45, u4ehi4]
    · linarith only [h1, hlam, hphi, ht45, u4ehi3, u5elo4]
  · linarith only [h0, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem r1l7_11_12_14_25_L_R_L_R_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h2, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · linarith only [h0, h2, h4, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
            · linarith only [h4, h8, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
              · linarith only [h0, h10, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
              · linarith only [h10, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
        · linarith only [h14, h2, hc23, hlam, hphi, u2ehi4]
        · linarith only [h14, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h18 | h18
    · linarith only [h0, h18, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
      · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
        · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
          · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
            · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
              · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                · linarith only [h20, h23, h25, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h25, hlam, hphi, ht45, u4ehi3, u5elo4]
              · linarith only [h23, h24, hlam, hphi, ht45, u4ehi2, u5elo3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
              · linarith only [h20, h22, h23, h29, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
              · linarith only [h29, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
          · linarith only [h18, h22, hc34, hlam, hphi, ht12, ht23, u1ehi0]
        · linarith only [h21, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
      · linarith only [h0, h20, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_11_12_14_L_0_L_R_L_0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h4, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
            · linarith only [h3, h5, hc34, hlam, hphi, u4elo1]
          · linarith only [h4, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
        · linarith only [h1, h3, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
      · linarith only [h0, h2, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
    · linarith only [h0, h12, hc23, hlam, hphi, u2ehi3]
    · linarith only [h12, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]

theorem r1l7_11_12_14_L_0_L_R_L_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
            · linarith only [h0, h3, h5, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
            · linarith only [h0, h3, h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
            · linarith only [h0, h12, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                · linarith only [h1, h15, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                · linarith only [h11, h15, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                · linarith only [h1, h18, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                · linarith only [h1, h11, h18, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
            · linarith only [h0, h21, h3, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
              · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                · linarith only [h1, h11, h24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
                · linarith only [h21, h23, h24, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                · linarith only [h0, h11, h27, h3, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                  · linarith only [h0, h11, h29, h3, hc34, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h0, h29, h3, hc45, hlam, hphi, ht23, ht34, u2ehi2]
      · linarith only [h0, h2, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
    · linarith only [h0, h34, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
      · linarith only [h0, h36, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h38 | h38
        · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
          · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
            · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
              · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                  · linarith only [h38, h43, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi4]
                  · linarith only [h38, h39, h43, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi3]
                · linarith only [h38, h39, h42, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
              · linarith only [h0, h41, hc35, hlam, hphi, ht23, u2ehi1]
            · linarith only [h0, h40, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
            · rcases m.htr 2 3 5 (by decide) (by decide) with h50 | h50
              · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
                · linarith only [h34, h39, h51, hc24, hlam, hphi, u2ehi1]
                · linarith only [h34, h51, hc45, hlam, hphi, ht23, ht34, u2ehi1]
              · linarith only [h0, h50, hc35, hlam, hphi, ht23, u2ehi1]
            · linarith only [h0, h38, h49, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi1]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
          · rcases m.htr 2 3 4 (by decide) (by decide) with h57 | h57
            · linarith only [h0, h38, h57, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h57, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
            · linarith only [h0, h38, h60, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h60, hc34, hlam, hphi, ht23, u2ehi1]

theorem r1l7_11_12_14_L_R_L_R_L_0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h3, h6, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h5, h8, hc34, hlam, hphi, u4elo1]
                · linarith only [h5, h7, hc24, hlam, hphi, u4elo1]
              · linarith only [h6, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
            · linarith only [h5, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
          · linarith only [h15, h3, hc23, hlam, hphi, u2ehi3]
          · linarith only [h15, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
      · linarith only [h1, h2, hc15, hlam, hphi, u1ehi2]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
    · linarith only [h0, h20, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h22 | h22
      · linarith only [h0, h22, hc12, hlam, hphi, u1ehi4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
        · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
          · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
            · linarith only [h22, h26, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
            · linarith only [h26, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
          · linarith only [h25, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
        · linarith only [h0, h24, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_11_12_25_L_0_L_0_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
      · linarith only [h0, h1, h3, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h6 | h6
    · linarith only [h0, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
      · linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi2]
      · linarith only [h0, h8, hc01, hlam, hphi, ht12, u2elo4]

theorem r1l7_11_12_25_L_0_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4, u2ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4 | h4
    · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h6 | h6
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
          · linarith only [h8, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
          · linarith only [h0, h6, h8, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h6, h7, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
        · linarith only [h12, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
          · linarith only [h14, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
            · linarith only [h16, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
              · linarith only [h0, h12, h16, h18, hc23, hlam, hphi, u2ehi0]
              · linarith only [h18, h6, hc35, hlam, hphi, ht23, u2ehi0]

theorem r1l7_11_12_25_L_0_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc24 := m.hcor 2 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
      · linarith only [h2, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
    · linarith only [h0, h6, hc24, hlam, hphi, u2ehi4]
    · linarith only [h6, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]

theorem r1l7_11_12_25_L_R_L_0_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi2]
  · linarith only [h0, hlam, hphi, ht12, u1ehi1, u2elo4]

theorem r1l7_11_12_25_L_R_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
          · linarith only [h4, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
        · linarith only [h2, h8, hc24, hlam, hphi, u2ehi4]
        · linarith only [h8, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h12 | h12
    · linarith only [h0, h12, hc12, hlam, hphi, u1ehi4]
    · linarith only [h12, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem r1l7_11_13_14_L_R_L_0_L_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h2, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · linarith only [h1, h3, h5, hc23, hlam, hphi, u3elo0]
          · linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
        · linarith only [h3, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
      · linarith only [h2, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
    · linarith only [h0, h12, hc12, hlam, hphi, u1ehi2]
    · linarith only [h12, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_11_13_25_L_0_L_0_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
      · linarith only [h0, h1, h3, hc23, hlam, hphi, u3elo4]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
    · linarith only [h6, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
      · linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi3]
      · linarith only [h0, h8, hc12, hlam, hphi, ht23, u3elo4]

theorem r1l7_11_13_25_L_0_L_0_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
            · linarith only [h2, h3, h4, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
              · linarith only [h2, h3, h4, h6, h8, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h3, h4, h8, hc23, hlam, hphi, u3elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
          · linarith only [h11, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
            · linarith only [h1, h13, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
              · linarith only [h13, h15, h3, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h15, h3, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
        · linarith only [h0, h18, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
          · linarith only [h1, h18, h2, h20, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
            · linarith only [h1, h2, h22, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
            · linarith only [h1, h18, h2, h22, hc12, hlam, hphi, ht23, u3elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h26 | h26
    · rcases m.htr 0 1 5 (by decide) (by decide) with h27 | h27
      · linarith only [h0, h27, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
        · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
          · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
            · linarith only [h26, h27, h30, h31, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
            · linarith only [h26, h27, h29, h31, hc23, hlam, hphi, u3elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
            · linarith only [h26, h34, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
            · linarith only [h0, h26, h30, h34, hc13, hlam, hphi, u3elo4]
        · linarith only [h0, h26, h29, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h38 | h38
      · linarith only [h26, h38, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
        · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
          · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
            · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
              · linarith only [h40, h43, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
              · linarith only [h42, h43, hc23, hlam, hphi, u3elo1]
            · linarith only [h26, h42, hc01, hlam, hphi, ht12, ht23, u3elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
            · linarith only [h40, h41, h47, hlam]
            · linarith only [h26, h47, hc01, hlam, hphi, ht12, ht23, u3elo4]
        · linarith only [h0, h40, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_11_13_25_L_0_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
    · linarith only [h0, h1, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
    · linarith only [h4, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
      · linarith only [h6, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
        · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
            · linarith only [h0, h10, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h0, h10, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h8, h9, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
          · linarith only [h0, h14, h6, h8, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
            · linarith only [h0, h16, h6, hc34, hlam, hphi, u3ehi1]
            · linarith only [h0, h16, hc45, hlam, hphi, ht34, u3ehi1]

theorem r1l7_11_13_25_L_0_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi9]
          · linarith only [h4, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
        · linarith only [h1, h3, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
    · linarith only [h0, h1, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc34, hlam, hphi, u3ehi4]
    · linarith only [h10, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]

theorem r1l7_11_13_25_L_R_L_0_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 1 3 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi3]
  · linarith only [h0, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]

theorem r1l7_11_13_25_L_R_L_0_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
          · linarith only [h1, h3, h4, hc23, hlam, hphi, u3elo0]
        · linarith only [h3, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
      · linarith only [h2, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc12, hlam, hphi, u1ehi2]
    · linarith only [h10, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_11_13_25_L_R_L_0_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
          · linarith only [h1, h3, h4, hc23, hlam, hphi, u3elo0]
        · linarith only [h3, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
      · linarith only [h2, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc12, hlam, hphi, u1ehi2]
    · linarith only [h10, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_11_14_25_L_0_L_0_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1elo := hb1.1
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
        · linarith only [h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
        · linarith only [h0, h1, h5, hc13, hlam, hphi, ht34, u4elo4]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h8 | h8
    · linarith only [h0, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
      · linarith only [h10, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
        · linarith only [h12, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
          · linarith only [h0, h10, h12, h14, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · linarith only [h0, h10, h14, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]

theorem r1l7_11_14_25_L_0_L_0_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
            · linarith only [h4, h5, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
            · linarith only [h4, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi7]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
              · linarith only [h1, h10, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
              · linarith only [h10, h3, hc14, hlam, hphi, u4elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
            · linarith only [h0, h14, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
            · linarith only [h13, h14, hc24, hlam, hphi, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17 | h17
            · linarith only [h1, h13, h17, h3, hlam, hphi, u5ehi7, u5elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
              · linarith only [h1, h19, h3, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h22, h3, hc04, hlam, hphi, u4elo2]
                  · linarith only [h13, h22, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h1, h13, h21, h25, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h13, h25, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h30 | h30
    · rcases m.htr 0 1 5 (by decide) (by decide) with h31 | h31
      · linarith only [h0, h31, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi6]
      · linarith only [h30, h31, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h34 | h34
      · linarith only [h30, h34, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi6]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
        · rcases m.htr 1 2 4 (by decide) (by decide) with h37 | h37
          · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
            · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
              · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                  · linarith only [h37, h41, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
                  · linarith only [h30, h36, h40, h41, hc34, hlam, hphi, u4elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                  · linarith only [h37, h44, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
                  · linarith only [h30, h36, h44, hc24, hlam, hphi, u4elo1]
              · linarith only [h30, h36, h39, hlam]
            · linarith only [h0, h30, h36, h38, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1, u5ehi9, u5elo2]
          · linarith only [h0, h37, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
          · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
            · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
              · linarith only [h36, h52, hc04, hlam, hphi, u4elo1]
              · linarith only [h30, h52, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
            · linarith only [h50, h51, hc24, hlam, hphi, ht45, u5elo2]
          · linarith only [h0, h50, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

theorem r1l7_11_14_25_L_R_L_0_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                    · rcases h5bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, h4, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h3, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h6, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h3, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h5, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hc35, hlam, hphi, ht12, ht23, p10_1, u1ehi4]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h9, hlam, hphi, ht12, ht23, ht34, p10_1, u1ehi4, u4elo3]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo3]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p10_1, u4elo3]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h7, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h8, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h9, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                    · linarith only [h4, h9, hc34, hlam, hphi, u4elo0]
                  · linarith only [h1, h7, h8, hc24, hlam, hphi, u4elo0]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h3, h4, h6, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo0]
            · linarith only [h5, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
          · linarith only [h1, h4, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h42 | h42
          · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
            · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
              · linarith only [h0, h3, h44, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                · linarith only [h43, h44, h46, hlam]
                · linarith only [h46, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
            · linarith only [h43, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
          · linarith only [h1, h42, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h53 | h53
    · linarith only [h0, h53, hc12, hlam, hphi, u1ehi3]
    · linarith only [h53, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem r1l7_11_14_25_L_R_L_0_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
  · linarith only [h0, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]

theorem r1l7_11_14_25_L_R_L_0_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · linarith only [h1, h3, h4, hc24, hlam, hphi, u4elo0]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc12, hlam, hphi, u1ehi3]
    · linarith only [h10, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem r1l7_11_14_25_L_R_L_0_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h4, h8, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · linarith only [h7, h9, hc24, hlam, hphi, u4elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · linarith only [h12, h7, hc24, hlam, hphi, u4elo1]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h6, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
            · linarith only [h4, h5, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h19, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
              · linarith only [h18, h19, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h18, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
        · linarith only [h2, h3, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h24 | h24
        · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
          · linarith only [h0, h2, h24, h25, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
            · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
              · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                    · linarith only [h0, h2, h27, h31, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                    · linarith only [h29, h31, hc24, hlam, hphi, u4elo1]
                  · linarith only [h0, h2, h30, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h29, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h28, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
            · linarith only [h27, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
        · linarith only [h0, h24, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h40 | h40
    · linarith only [h0, h40, hc12, hlam, hphi, u1ehi4]
    · linarith only [h40, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem r1l7_11_14_25_L_R_L_R_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have h5emax := hb5.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · rcases h5emax with h3 | h3 | h3 | h3 | h3
        · linarith only [h0, h3, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h3, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h1, h3, hlam, ht45, u4ehi4]
        · linarith only [h2, h3, hlam, ht45, u4ehi4]
        · linarith only [h3, hlam, ht45, u4ehi4]
      · rcases h5emax with h9 | h9 | h9 | h9 | h9
        · linarith only [h0, h9, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h9, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h1, h2, h9, hlam, ht45, u4ehi3]
        · linarith only [h2, h9, hlam, ht45, u4ehi3]
        · linarith only [h2, h9, hlam, ht45, u4ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
      · rcases h5emax with h16 | h16 | h16 | h16 | h16
        · linarith only [h0, h16, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h16, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h1, h16, hlam, ht45, u4ehi2]
        · linarith only [h1, h15, h16, hlam, ht45, u4ehi2]
        · linarith only [h1, h16, hlam, ht45, u4ehi2]
      · rcases h5emax with h22 | h22 | h22 | h22 | h22
        · linarith only [h0, h22, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h22, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h1, h22, hlam, ht45, u4ehi2]
        · linarith only [h15, h22, hlam, ht45, u4ehi3]
        · linarith only [h1, h22, hlam, ht45, u4ehi2]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
    · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
      · rcases h5emax with h30 | h30 | h30 | h30 | h30
        · linarith only [h0, h30, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h0, h30, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h28, h30, hlam, ht45, u4ehi4]
        · linarith only [h29, h30, hlam, ht45, u4ehi4]
        · linarith only [h30, hlam, ht45, u4ehi4]
      · rcases h5emax with h36 | h36 | h36 | h36 | h36
        · linarith only [h0, h36, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h0, h36, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h28, h29, h36, hlam, ht45, u4ehi3]
        · linarith only [h29, h36, hlam, ht45, u4ehi3]
        · linarith only [h29, h36, hlam, ht45, u4ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
      · rcases h5emax with h43 | h43 | h43 | h43 | h43
        · linarith only [h0, h43, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h0, h43, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h28, h43, hlam, ht45, u4ehi2]
        · linarith only [h42, h43, hlam, ht45, u4ehi4]
        · linarith only [h43, hlam, ht45, u4ehi4]
      · rcases h5emax with h49 | h49 | h49 | h49 | h49
        · linarith only [h0, h49, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h0, h49, hlam, ht12, ht23, ht34, ht45, u1ehi0]
        · linarith only [h28, h49, hlam, ht45, u4ehi2]
        · linarith only [h42, h49, hlam, ht45, u4ehi3]
        · linarith only [h28, h49, hlam, ht45, u4ehi2]

theorem r1l7_11_14_25_L_R_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, h4, h5, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                    · linarith only [h11, hlam, hphi, ht45, u4ehi2, u5elo4]
              · linarith only [h5, h6, hlam, hphi, ht45, u4ehi1, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                · linarith only [h15, h16, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h18, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · linarith only [h15, h18, h5, hc23, hc34, hlam, hphi]
              · linarith only [h15, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
            · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
              · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                      · linarith only [h1, h22, h27, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h27, hlam, hphi, ht45, u4ehi3, u5elo4]
                    · linarith only [h26, hlam, hphi, ht45, u4ehi2, u5elo4]
                  · linarith only [h23, h25, h3, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                · linarith only [h24, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h22, h23, hlam, hphi, ht45, u4ehi3, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
              · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                · linarith only [h22, h34, h35, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · linarith only [h35, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h34, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h42 | h42
    · linarith only [h0, h42, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h44 | h44
      · linarith only [h0, h44, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h46 | h46
        · linarith only [h0, h46, hc12, hlam, hphi, u1ehi4]
        · linarith only [h46, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem r1l7_11_23_L_0_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_L m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3elo := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · linarith only [h4, hc23, hlam, hphi, u3elo4]
        · linarith only [h3, hc13, hlam, hphi, u3elo3]
      · linarith only [h2, hc12, hlam, hphi, ht23, u3elo2]
    · linarith only [h1, hc01, hlam, hphi, ht12, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
      · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
        · linarith only [h0, h10, h12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
        · linarith only [h12, hc13, hlam, hphi, u3elo3]
      · linarith only [h0, h11, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · linarith only [h10, hc01, hlam, hphi, ht12, ht23, u3elo1]

theorem r1l7_11_23_L_0_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
  · linarith only [h0, hc34, hlam, hphi, u3ehi1]

theorem r1l7_11_23_L_R_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_L m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  linarith only [hlam, hphi, ht12, ht23, u1ehi2, u3elo1]

theorem r1l7_11_23_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
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
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h8 | h8
    · linarith only [h0, h8, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
          · linarith only [h10, h12, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h12, hc34, hlam, hphi, u3ehi2]
        · linarith only [h11, h8, hc34, hlam, hphi, ht12, ht23, u1ehi0]
      · linarith only [h0, h10, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_11_23_L_R_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h3, h6, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · rcases h3bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hc13, hlam, hphi, p10_1, u3elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hc23, hlam, hphi, p10_1, u3elo0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      rcases p10_3 (m.d 0 3) (by simp) with h14 | h14
                      · rcases p10_3 (m.d 1 3) (by simp) with h15 | h15
                        · linarith only [h1, h15, hlam]
                        · linarith only [h15, h4, hlam]
                      · linarith only [h14, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      rcases p10_3 (m.d 0 3) (by simp) with h19 | h19
                      · rcases p10_3 (m.d 1 3) (by simp) with h20 | h20
                        · linarith only [h1, h20, hlam]
                        · linarith only [h20, h5, hlam]
                      · linarith only [h19, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h7, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p10_1, u3elo1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      rcases p10_3 (m.d 0 3) (by simp) with h27 | h27
                      · rcases p10_3 (m.d 1 3) (by simp) with h28 | h28
                        · rcases p10_3 (m.d 2 3) (by simp) with h29 | h29
                          · linarith only [h29, h3, hlam]
                          · linarith only [h29, h6, hlam]
                        · linarith only [h28, hlam, p10_0]
                      · linarith only [h1, h27, h7, h8, hlam, hphi, ht12, ht23, u1ehi2, u3elo2]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      rcases p10_3 (m.d 0 3) (by simp) with h34 | h34
                      · rcases p10_3 (m.d 1 3) (by simp) with h35 | h35
                        · rcases p10_3 (m.d 2 3) (by simp) with h36 | h36
                          · linarith only [h3, h36, hlam]
                          · linarith only [h36, h7, hlam]
                        · linarith only [h35, hlam, p10_0]
                      · linarith only [h1, h34, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h3, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h3, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h3, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h1, h5, hlam, hphi, ht12, ht23, p10_1, u1ehi4, u3elo3]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h4, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h6, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h8, hlam, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h1, h3, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p10_1, u1ehi4]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h5, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h7, hlam, p10_0]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [h0, h3, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1]
                    · have p10_0 := h10c.1
                      have p10_1 := h10c.2.1
                      have p10_2 := h10c.2.2.1
                      have p10_3 := h10c.2.2.2
                      linarith only [hlam, p10_0]
                · linarith only [h1, h5, h7, hc23, hlam, hphi, u3elo0]
              · linarith only [h1, h4, h6, hc23, hlam, hphi, u3elo0]
            · linarith only [h5, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
          · linarith only [h4, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
        · linarith only [h3, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h63 | h63
    · linarith only [h0, h63, hc12, hlam, hphi, u1ehi2]
    · linarith only [h63, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_11_25_L_R_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h5elo := hb5.1
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo1]

theorem r1l7_12_13_25_L_0_L_0_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
      · linarith only [h0, h1, h3, hc23, hlam, hphi, u3elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
    · linarith only [h0, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
      · linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi3]
      · linarith only [h0, h8, hc02, hlam, hphi, ht23, u3elo4]

theorem r1l7_12_13_25_L_0_L_R_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
    · linarith only [h0, h1, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
    · linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
      · linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
        · linarith only [h0, h6, h8, hc34, hlam, hphi, u3ehi2]
        · linarith only [h0, h8, hc45, hlam, hphi, ht34, u3ehi2]

theorem r1l7_12_13_25_L_0_L_R_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
      · linarith only [h2, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
    · linarith only [h1, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
    · linarith only [h0, h6, hc34, hlam, hphi, u3ehi4]
    · linarith only [h6, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]

theorem r1l7_12_13_25_L_R_L_0_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi3]
    · linarith only [h1, hlam, hphi, ht23, u2ehi2, u3elo4]
  · linarith only [h0, hlam, hphi, ht23, u2ehi2, u3elo3]

theorem r1l7_12_13_25_L_R_L_R_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 4 5 (by decide) (by decide) with h1 | h1
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
          linarith only [hc05, hlam, hphi, p3_1, u5elo1]
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
          linarith only [hlam, hphi, ht34, ht45, p3_1, u3ehi4, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc45, hlam, hphi, p3_1, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc05, hlam, hphi, p3_1, u5elo2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, hphi, ht34, ht45, p3_1, u3ehi4, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc45, hlam, hphi, p3_1, u5elo1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc05, hlam, hphi, p3_1, u5elo3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc15, hlam, hphi, p3_1, u5elo3]
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
          linarith only [hc05, hlam, hphi, p3_1, u5elo4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, h1, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, p3_0]
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
      · linarith only [h0, h1, h2, hlam, hphi, ht34, ht45, u3ehi3, u5elo1]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
  · linarith only [h0, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]

theorem r1l7_12_13_25_L_R_L_R_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h3, h5, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
            · linarith only [h5, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
          · linarith only [h4, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
          · linarith only [h3, h9, hc34, hlam, hphi, u3ehi4]
          · linarith only [h9, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
      · linarith only [h2, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
    · linarith only [h0, h14, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
      · linarith only [h0, h16, hc23, hlam, hphi, u2ehi4]
      · linarith only [h16, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]

theorem r1l7_12_14_25_L_0_L_0_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
      · linarith only [h0, h1, h3, hc34, hlam, hphi, u4elo4]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
    · linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
      · linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
      · linarith only [h0, h8, hc23, hlam, hphi, ht34, u4elo4]

theorem r1l7_12_14_25_L_0_L_R_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi2]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
      · linarith only [h1, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
        · linarith only [h0, h1, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
          · linarith only [h0, h1, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
            · linarith only [h11, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
            · linarith only [h0, h1, h11, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
    · linarith only [h0, h14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
      · linarith only [h0, h16, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
        · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
          · linarith only [h19, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
            · linarith only [h18, h19, h21, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
              · linarith only [h14, h18, h19, h21, h23, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h18, h19, h23, hc45, hlam, hphi, u4ehi3]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
          · linarith only [h26, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
            · linarith only [h28, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
              · linarith only [h0, h18, h28, h30, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h0, h18, h30, hc12, hc45, hlam, hphi, ht23, ht34]

theorem r1l7_12_14_25_L_0_L_R_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h2, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
            · linarith only [h5, hlam, hphi, ht45, u4ehi2, u5elo4]
          · linarith only [h1, h4, hlam, hphi, ht45, u4ehi1, u5elo0]
        · linarith only [h0, h3, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
        · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
            · linarith only [h10, h12, h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
            · linarith only [h11, h12, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
          · linarith only [h11, hlam, hphi, ht45, u4ehi1, u5elo4]
        · linarith only [h0, h10, hc12, hlam, hphi, u2elo0]
    · linarith only [h1, hlam, hphi, ht45, u4ehi0, u5elo4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
    · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
      · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
        · linarith only [h0, h20, hc02, hlam, hphi, u2elo1]
        · linarith only [h19, h20, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
        · linarith only [h0, h19, h23, hc02, hlam, hphi, u2elo3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
          · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
            · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
              · rcases h5bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, p28_0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hc15, hlam, hphi, p28_1, u5elo0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h0, hlam, p28_0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, p28_1, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h0, hlam, hphi, ht45, p28_1, u4ehi4, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hc05, hlam, hphi, p28_1, u5elo1]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, p28_0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h23, hlam, p28_0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h23, h27, hlam, hphi, ht45, p28_1, u4ehi4, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h23, hlam, hphi, ht45, p28_1, u4ehi4, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h18, hlam, hphi, ht45, p28_1, u4ehi4, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hc15, hlam, hphi, p28_1, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, p28_0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h27, hlam, hphi, ht45, p28_1, u4ehi4, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, hphi, ht45, p28_1, u4ehi4, u5elo2]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h18, hlam, hphi, ht45, p28_1, u4ehi4, u5elo3]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h25, hlam, hphi, ht45, p28_1, u4ehi4, u5elo3]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hc25, hlam, hphi, p28_1, u5elo3]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, p28_0]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, hphi, ht45, p28_1, u4ehi4, u5elo3]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h18, hlam, p28_1]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h25, hlam, p28_1]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h26, hlam, p28_1]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [h27, hlam, p28_1]
                · have p28_0 := h28c.1
                  have p28_1 := h28c.2.1
                  have p28_2 := h28c.2.2.1
                  have p28_3 := h28c.2.2.2
                  linarith only [hlam, p28_0]
              · linarith only [h18, h27, hlam, hphi, ht45, u4ehi3, u5elo0]
            · linarith only [h19, h25, h26, hlam]
          · linarith only [h25, hlam, hphi, ht45, u4ehi1, u5elo4]
    · linarith only [h18, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem r1l7_12_14_25_L_R_L_0_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
  · linarith only [h0, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]

theorem r1l7_12_14_25_L_R_L_0_M_IR (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
          · linarith only [h1, h3, h4, hc34, hlam, hphi, u4elo0]
        · linarith only [h3, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
      · linarith only [h2, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
    · linarith only [h1, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc23, hlam, hphi, u2ehi3]
    · linarith only [h10, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]

theorem r1l7_12_14_25_L_R_L_0_M_LR (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
          · linarith only [h3, h4, hc34, hlam, hphi, u4elo2]
        · linarith only [h3, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
      · linarith only [h2, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc23, hlam, hphi, u2ehi4]
    · linarith only [h10, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]

theorem r1l7_12_14_25_L_R_L_R_H_I (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5emax := hb5.2.2
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · rcases h5emax with h3 | h3 | h3 | h3 | h3
        · linarith only [h0, h3, hlam, ht45, u4ehi4]
        · linarith only [h1, h3, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h3, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h2, h3, hlam, ht45, u4ehi4]
        · linarith only [h3, hlam, ht45, u4ehi4]
      · rcases h5emax with h9 | h9 | h9 | h9 | h9
        · linarith only [h0, h2, h9, hlam, ht45, u4ehi3]
        · linarith only [h1, h9, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h9, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h2, h9, hlam, ht45, u4ehi3]
        · linarith only [h2, h9, hlam, ht45, u4ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
      · rcases h5emax with h16 | h16 | h16 | h16 | h16
        · linarith only [h0, h16, hlam, ht45, u4ehi4]
        · linarith only [h1, h16, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h1, h16, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h15, h16, hlam, ht45, u4ehi4]
        · linarith only [h16, hlam, ht45, u4ehi4]
      · rcases h5emax with h22 | h22 | h22 | h22 | h22
        · linarith only [h0, h15, h22, hlam, ht45, u4ehi3]
        · linarith only [h1, h22, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h1, h22, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h15, h22, hlam, ht45, u4ehi3]
        · linarith only [h15, h22, hlam, ht45, u4ehi3]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
    · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
      · rcases h5emax with h30 | h30 | h30 | h30 | h30
        · linarith only [h0, h30, hlam, ht45, u4ehi0]
        · linarith only [h28, h30, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h30, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h29, h30, hlam, ht45, u4ehi4]
        · linarith only [h30, hlam, ht45, u4ehi4]
      · rcases h5emax with h36 | h36 | h36 | h36 | h36
        · linarith only [h0, h36, hlam, ht45, u4ehi0]
        · linarith only [h28, h36, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h36, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h29, h36, hlam, ht45, u4ehi3]
        · linarith only [h0, h36, hlam, ht45, u4ehi0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
      · rcases h5emax with h43 | h43 | h43 | h43 | h43
        · linarith only [h0, h43, hlam, ht45, u4ehi0]
        · linarith only [h28, h43, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h28, h43, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h0, h42, h43, hlam, ht45, u4ehi0]
        · linarith only [h0, h43, hlam, ht45, u4ehi0]
      · rcases h5emax with h49 | h49 | h49 | h49 | h49
        · linarith only [h0, h49, hlam, ht45, u4ehi0]
        · linarith only [h28, h49, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h28, h49, hlam, ht23, ht34, ht45, u2ehi1]
        · linarith only [h42, h49, hlam, ht45, u4ehi3]
        · linarith only [h0, h49, hlam, ht45, u4ehi0]

theorem r1l7_12_14_25_L_R_L_R_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · rcases h5emax with h3 | h3 | h3 | h3 | h3
        · linarith only [h0, h3, hlam, ht45, u4ehi4]
        · linarith only [h1, h3, hlam, ht45, u4ehi4]
        · linarith only [h3, hlam, ht23, ht34, ht45, u2ehi4]
        · linarith only [h2, h3, hlam, ht45, u4ehi4]
        · linarith only [h3, hlam, ht45, u4ehi4]
      · linarith only [h0, h2, hlam, hphi, ht45, u4ehi3, u5elo0]
    · linarith only [h0, h1, hlam, hphi, ht45, u4ehi1, u5elo0]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem r1l7_12_23_L_0_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 4 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
    · linarith only [h1, hc34, hlam, hphi, u3ehi2]
  · linarith only [h0, hc34, hlam, hphi, u3ehi1]

theorem r1l7_12_23_L_R_H_L (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_L m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  linarith only [hlam, hphi, ht23, u2ehi2, u3elo2]

theorem r1l7_12_24_L_0_H_L (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4elo := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h2, h5, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
              · linarith only [h6, hc34, hlam, hphi, u4elo4]
            · linarith only [h5, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h4, hc13, hlam, hphi, ht34, u4elo3]
        · linarith only [h3, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
            · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h12, h14, h15, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h15, hc34, hlam, hphi, u4elo4]
            · linarith only [h14, h2, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h12, h13, h2, hc24, hlam, hphi, u4elo3]
        · linarith only [h12, hc12, hlam, hphi, ht23, ht34, u4elo2]
    · linarith only [h1, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h22 | h22
    · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
        · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
          · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
            · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
              · linarith only [h0, h22, h24, h26, h27, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h27, hc34, hlam, hphi, u4elo4]
            · linarith only [h26, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h25, hc13, hlam, hphi, ht34, u4elo3]
        · linarith only [h0, h24, hc01, hlam, hphi, ht12, u2elo3]
      · linarith only [h0, h22, h23, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
    · linarith only [h22, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem r1l7_12_24_L_0_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi2]

theorem r1l7_12_24_L_R_H_L (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  linarith only [hlam, hphi, ht23, ht34, u2ehi3, u4elo2]

theorem r1l7_12_24_L_R_H_R (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
          · linarith only [h1, h5, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
          · linarith only [h5, hc45, hlam, hphi, u4ehi2]
      · linarith only [h2, hc45, hlam, hphi, u4ehi1]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
      · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
        · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
          · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
            · linarith only [h13, h15, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h12, h15, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · linarith only [h10, h12, h14, hlam]
        · linarith only [h0, h13, hc34, hlam, hphi, ht23, u2ehi1]
      · linarith only [h12, hc45, hlam, hphi, u4ehi1]

theorem r1l7_12_25_L_R_H_L (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  linarith only [hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo2]

theorem r1l7_12_25_L_R_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
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
            linarith only [h0, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, hphi, ht23, ht34, ht45, p4_1, u2ehi4, u5elo1]
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
            linarith only [h1, hlam, p4_1]
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
            linarith only [hc35, hlam, hphi, p4_1, u5elo2]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, hc45, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, hc35, hlam, hphi, ht23, p4_1, u2ehi4]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, h2, hc15, hlam, hphi, p4_1, u5elo0]
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
            linarith only [h1, h2, hc45, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, hc45, hlam, hphi, ht23, ht34, p4_1, u2ehi4]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, h3, hc15, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h3, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, h3, hc35, hlam, hphi, p4_1, u5elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
      · linarith only [h2, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h33 | h33
    · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
      · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
        · rcases h5bigk with h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hlam, p36_0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, hlam, p36_1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, hc25, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, hc35, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hc05, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hlam, p36_0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hlam, hphi, ht23, ht34, ht45, p36_1, u2ehi4, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hc35, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hc45, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, hlam, p36_1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, hc15, hlam, hphi, p36_1, u5elo0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hlam, p36_0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, hc35, hlam, hphi, p36_1, u5elo0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, h33, hc45, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, hc35, hlam, hphi, ht23, p36_1, u2ehi4]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, h34, hc15, hlam, hphi, p36_1, u5elo0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h34, hlam, p36_0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hlam, p36_0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, h33, h34, hc45, hlam, hphi, p36_1, u5elo1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, hc45, hlam, hphi, ht23, ht34, p36_1, u2ehi4]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h0, h33, h35, hlam, p36_1]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h35, hlam, p36_0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [h33, h35, hc35, hlam, hphi, p36_1, u5elo0]
          · have p36_0 := h36c.1
            have p36_1 := h36c.2.1
            have p36_2 := h36c.2.2.1
            have p36_3 := h36c.2.2.2
            linarith only [hlam, p36_0]
        · linarith only [h35, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
      · linarith only [h34, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
    · linarith only [h33, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_13_24_L_0_H_L (m : N7Model)
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h3, h6, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h7, hc34, hlam, hphi, u4elo4]
              · linarith only [h6, hc23, hlam, hphi, ht34, u4elo3]
            · linarith only [h5, hc13, hlam, hphi, ht34, u4elo3]
          · linarith only [h4, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
              · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                · linarith only [h13, h15, h16, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h16, hc34, hlam, hphi, u4elo4]
              · linarith only [h15, h3, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h13, h14, h3, hc24, hlam, hphi, u4elo3]
          · linarith only [h13, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h24 | h24
    · rcases m.htr 0 1 4 (by decide) (by decide) with h25 | h25
      · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
        · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
            · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
              · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                · linarith only [h0, h24, h26, h29, h30, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h30, hc34, hlam, hphi, u4elo4]
              · linarith only [h29, hc23, hlam, hphi, ht34, u4elo3]
            · linarith only [h28, hc13, hlam, hphi, ht34, u4elo3]
          · linarith only [h0, h27, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h0, h24, h26, hc13, hlam, hphi, u3elo2]
      · linarith only [h24, h25, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h38 | h38
      · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
        · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
          · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
            · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
              · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                · linarith only [h24, h38, h40, h42, h43, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                · linarith only [h43, hc34, hlam, hphi, u4elo4]
              · linarith only [h24, h38, h40, h42, hc23, hc24, hlam, hphi, u3elo1, u4elo3]
            · linarith only [h24, h38, h40, h41, hc24, hlam, hphi, u4elo3]
          · linarith only [h24, h39, h40, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h0, h38, h39, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
      · linarith only [h38, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem r1l7_13_24_L_0_H_R (m : N7Model)
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi3]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
    · linarith only [h2, hc45, hlam, hphi, u4ehi1]

theorem r1l7_13_24_L_R_H_L (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  linarith only [hlam, hphi, ht34, u3ehi3, u4elo3]

theorem r1l7_13_25_L_R_H_L (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  linarith only [hlam, hphi, ht34, ht45, u3ehi4, u5elo3]

theorem r1l7_13_25_L_R_M_LI (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
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
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · rcases h5bigk with h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc15, hlam, hphi, p7_1, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc25, hlam, hphi, p7_1, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc35, hlam, hphi, p7_1, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc45, hlam, hphi, p7_1, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc05, hlam, hphi, p7_1, u5elo1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h4, hlam, hphi, ht34, ht45, p7_1, u3ehi4, u5elo1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, hphi, ht34, ht45, p7_1, u3ehi4, u5elo1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc45, hlam, hphi, p7_1, u5elo1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, hlam, hphi, ht34, ht45, p7_1, u3ehi4, u5elo2]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc15, hlam, hphi, p7_1, u5elo2]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, hphi, ht34, ht45, p7_1, u3ehi4, u5elo2]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc45, hlam, hphi, p7_1, u5elo2]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h4, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, p7_1, u5elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht34, p7_1, u3ehi4]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, h6, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h5, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h6, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
              · linarith only [h6, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
            · linarith only [h3, h5, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
          · linarith only [h0, h4, hlam, hphi, ht34, ht45, u3ehi2, u5elo0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
          · linarith only [h3, h36, hc34, hlam, hphi, u3ehi4]
          · linarith only [h0, h36, hlam, hphi, ht34, ht45, u3ehi2, u5elo0]
      · linarith only [h0, h2, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
      · linarith only [h1, h40, hc34, hlam, hphi, u3ehi4]
      · linarith only [h40, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
  · linarith only [h0, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem r1l7_14_25_L_R_H_L (m : N7Model)
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem r1l7_14_25_L_R_M_LI (m : N7Model)
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hlam, hphi, ht45, u4ehi3, u5elo0]
      · linarith only [h0, h2, hlam, hphi, ht45, u4ehi2, u5elo0]
    · linarith only [h0, h1, hlam, hphi, ht45, u4ehi1, u5elo0]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem r1l7_20_11_13_14_H_I_L_0_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases h0emin with h2 | h2 | h2 | h2 | h2
      · linarith only [h2, hlam, ht01, u1elo0]
      · linarith only [h0, h2, hlam, ht01, u1elo0]
      · linarith only [h2, hlam, ht01, ht12, ht23, u3elo0]
      · linarith only [h2, hlam, ht01, ht12, ht23, ht34, u4elo0]
      · linarith only [h1, h2, hlam, ht01, ht12, ht23, u3elo0]
    · rcases h0emin with h8 | h8 | h8 | h8 | h8
      · linarith only [h8, hlam, ht01, u1elo0]
      · linarith only [h0, h8, hlam, ht01, u1elo0]
      · linarith only [h1, h8, hlam, ht01, ht12, ht23, u3elo4]
      · linarith only [h8, hlam, ht01, ht12, ht23, ht34, u4elo0]
      · linarith only [h1, h8, hlam, ht01, ht12, ht23, u3elo4]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h14 | h14
    · rcases h0emin with h15 | h15 | h15 | h15 | h15
      · linarith only [h0, h15, hlam, ht01, u1elo1]
      · linarith only [h0, h15, hlam, ht01, u1elo1]
      · linarith only [h15, hlam, ht01, ht12, ht23, u3elo0]
      · linarith only [h15, hlam, ht01, ht12, ht23, ht34, u4elo0]
      · linarith only [h14, h15, hlam, ht01, ht12, ht23, u3elo0]
    · rcases h0emin with h21 | h21 | h21 | h21 | h21
      · linarith only [h0, h21, hlam, ht01, u1elo1]
      · linarith only [h0, h21, hlam, ht01, u1elo1]
      · linarith only [h14, h21, hlam, ht01, ht12, ht23, u3elo4]
      · linarith only [h21, hlam, ht01, ht12, ht23, ht34, u4elo0]
      · linarith only [h14, h21, hlam, ht01, ht12, ht23, u3elo4]

theorem r1l7_20_11_13_14_H_I_L_0_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · rcases h0emin with h6 | h6 | h6 | h6 | h6
              · linarith only [h6, hlam, ht01, u1elo0]
              · linarith only [h0, h6, hlam, ht01, u1elo0]
              · linarith only [h1, h6, hlam, ht01, u1elo0]
              · linarith only [h6, hlam, ht01, ht12, ht23, ht34, u4elo0]
              · linarith only [h3, h6, hlam, ht01, ht12, ht23, ht34, u4elo0]
            · linarith only [h2, h4, h5, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · linarith only [h3, h4, hc14, hlam, hphi, u4elo0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
          · linarith only [h14, h3, hc04, hlam, hphi, u4elo1]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
            · linarith only [h16, h2, h3, hc14, hlam, hphi, u4elo3]
            · linarith only [h16, hlam, hphi, ht34, u3ehi3, u4elo4]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h20 | h20
      · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
        · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
          · linarith only [h1, h20, h22, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
          · linarith only [h21, h22, hc14, hlam, hphi, u4elo0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
          · linarith only [h21, h25, hc04, hlam, hphi, u4elo1]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
            · linarith only [h20, h21, h27, hc14, hlam, hphi, u4elo3]
            · linarith only [h27, hlam, hphi, ht34, u3ehi3, u4elo4]
      · linarith only [h0, h20, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h31 | h31
    · linarith only [h0, h31, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h33 | h33
      · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
        · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
          · linarith only [h0, h33, h35, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
          · linarith only [h34, h35, hc14, hlam, hphi, u4elo0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h38 | h38
          · linarith only [h34, h38, hc04, hlam, hphi, u4elo1]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h40 | h40
            · linarith only [h33, h34, h40, hc14, hlam, hphi, u4elo3]
            · linarith only [h40, hlam, hphi, ht34, u3ehi3, u4elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
        · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
          · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
            · rcases h0emin with h46 | h46 | h46 | h46 | h46
              · linarith only [h33, h46, hlam, ht01, ht12, ht23, ht34, u4elo1]
              · linarith only [h0, h46, hlam, ht01, u1elo1]
              · linarith only [h31, h46, hlam, ht01, u1elo2]
              · linarith only [h46, hlam, ht01, ht12, ht23, ht34, u4elo0]
              · linarith only [h43, h46, hlam, ht01, ht12, ht23, ht34, u4elo0]
            · linarith only [h33, h43, h45, hc34, hlam, hphi, u4elo1]
          · linarith only [h33, h43, h44, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
          · linarith only [h33, h43, h54, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
          · linarith only [h33, h54, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]

theorem r1l7_20_11_13_14_H_I_L_R_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases h0bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, h10, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h11, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi2]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h3, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h4, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h3, h8, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h3, hlam, hphi, ht12, ht23, p12_1, u1ehi4, u3elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h2, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, ht34, p12_1, u4elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h6, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h3, h6, hlam, hphi, ht12, ht23, p12_1, u1ehi4, u3elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h3, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h5, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h7, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h8, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                        · linarith only [h11, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
                      · linarith only [h10, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
                    · linarith only [h9, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
                  · linarith only [h2, h8, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
                · linarith only [h1, h7, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
              · linarith only [h1, h6, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h44 | h44
              · rcases m.htr 0 3 5 (by decide) (by decide) with h45 | h45
                · linarith only [h4, h45, h5, hlam]
                · linarith only [h2, h44, h45, hlam, hphi, ht12, ht23, u1ehi3, u3elo4]
              · linarith only [h1, h44, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
          · linarith only [h0, h4, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h53 | h53
    · linarith only [h0, h53, hc12, hlam, hphi, u1ehi2]
    · linarith only [h53, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_20_11_13_14_H_L_L_0_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
        · linarith only [h0, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
          · linarith only [h0, h1, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
              · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h10, h12, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                  · linarith only [h12, h3, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
                · linarith only [h11, h3, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h10, h4, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
          · linarith only [h0, h1, h19, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
            · linarith only [h0, h21, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
              · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                · linarith only [h24, h3, hc03, hlam, hphi, u3elo2]
                · linarith only [h17, h24, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h17, h23, hc12, hlam, hphi, ht23, u3elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h28 | h28
    · linarith only [h28, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h30 | h30
      · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
        · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
          · linarith only [h0, h28, h32, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
            · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
              · linarith only [h31, h32, h35, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h0, h32, h35, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
              · linarith only [h31, h38, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
              · linarith only [h0, h32, h38, hc01, hlam, hphi, ht12, ht23, u3elo3]
        · linarith only [h0, h31, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
        · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
          · linarith only [h0, h28, h43, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
            · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
              · linarith only [h42, h43, h46, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h0, h43, h46, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
              · linarith only [h42, h49, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
              · linarith only [h0, h43, h49, hc01, hlam, hphi, ht12, ht23, u3elo3]
        · linarith only [h0, h42, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_20_11_13_14_H_L_L_0_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
        · linarith only [h5, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h1, h3, h5, h8, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
              · linarith only [h0, h1, h10, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                · linarith only [h1, h12, h5, hc01, hlam, hphi, u1elo3]
                · linarith only [h0, h1, h12, h7, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
            · linarith only [h0, h15, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
              · linarith only [h0, h1, h17, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
                · linarith only [h1, h19, h5, hc01, hlam, hphi, u1elo3]
                · linarith only [h0, h1, h19, h7, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h22 | h22
    · linarith only [h22, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h24 | h24
      · linarith only [h24, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
        · linarith only [h26, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
          · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
            · linarith only [h0, h24, h29, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
              · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                · linarith only [h26, h32, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                · linarith only [h29, h31, h32, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                · linarith only [h26, h35, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                  · linarith only [h28, h37, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                    · linarith only [h28, h31, h39, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                      · linarith only [h22, h35, h41, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h29, h41, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
            · linarith only [h0, h24, h44, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h46 | h46
              · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                · linarith only [h26, h47, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                · linarith only [h44, h46, h47, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                · linarith only [h26, h50, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                  · linarith only [h0, h44, h52, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
                    · linarith only [h0, h46, h54, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                      · linarith only [h22, h50, h56, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h28, h52, h56, hc12, hc45, hlam, hphi, ht23, ht34]

theorem r1l7_20_11_13_14_H_L_L_0_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
        · linarith only [h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
        · linarith only [h0, h1, h3, h4, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
        · linarith only [h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h9 | h9
          · linarith only [h7, h9, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
            · linarith only [h0, h1, h11, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
              · linarith only [h0, h1, h13, h3, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                · linarith only [h1, h15, h7, hc01, hlam, hphi, u1elo2]
                · linarith only [h0, h1, h15, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h18 | h18
    · linarith only [h18, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h20 | h20
      · rcases m.htr 0 3 4 (by decide) (by decide) with h21 | h21
        · linarith only [h21, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h23 | h23
          · linarith only [h20, h21, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
            · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
              · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                · linarith only [h18, h21, h25, h27, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                  · linarith only [h25, h27, h29, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
                  · linarith only [h20, h29, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
              · linarith only [h20, h26, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
              · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
                · linarith only [h21, h34, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                · linarith only [h25, h33, h34, hlam]
              · linarith only [h0, h20, h33, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h38 | h38
        · linarith only [h38, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
          · linarith only [h38, h40, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
            · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
              · linarith only [h0, h20, h43, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                · linarith only [h38, h42, h43, h45, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                  · linarith only [h18, h45, h47, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h42, h43, h47, hc34, hlam, hphi, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
              · linarith only [h0, h20, h50, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
                · linarith only [h38, h52, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                  · linarith only [h0, h42, h52, h54, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h42, h54, hc01, hc34, hlam, hphi, ht12, ht23]

theorem r1l7_20_11_13_14_H_L_L_R_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
    · linarith only [h2, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_20_11_13_14_H_L_L_R_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
      · linarith only [h4, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
        · linarith only [h0, h2, h4, h6, hc14, hlam, hphi, u1ehi0]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
          · linarith only [h0, h2, h4, h8, hc34, hlam, hphi, ht12, ht23, u1ehi0]
          · linarith only [h0, h2, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]

theorem r1l7_20_11_13_14_M_IR_L_0_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases h0emin with h2 | h2 | h2 | h2 | h2
      · linarith only [h2, hlam, ht01, u1elo0]
      · linarith only [h0, h2, hlam, ht01, u1elo0]
      · linarith only [h2, hlam, ht01, ht12, ht23, u3elo0]
      · linarith only [h2, hlam, ht01, ht12, ht23, ht34, u4elo0]
      · linarith only [h1, h2, hlam, ht01, u1elo0]
    · linarith only [h1, hlam, hphi, ht01, u0ehi0, u1elo4]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem r1l7_20_11_13_14_M_IR_L_0_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases h0emin with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, u1elo0]
        · linarith only [h0, h3, hlam, ht01, u1elo0]
        · linarith only [h1, h3, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h2, h3, hlam, ht01, u1elo0]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi1]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi1, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem r1l7_20_11_13_14_M_IR_L_R_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h3, h6, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h2, h5, h8, hc34, hlam, hphi, u4elo0]
                · linarith only [h2, h5, h7, hc24, hlam, hphi, u4elo0]
              · linarith only [h1, h4, h6, hc23, hlam, hphi, u3elo0]
            · linarith only [h5, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
          · linarith only [h4, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
        · linarith only [h3, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h18 | h18
    · linarith only [h0, h18, hc12, hlam, hphi, u1ehi2]
    · linarith only [h18, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_20_11_13_14_M_IR_L_R_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · linarith only [h2, h5, hc23, hlam, hphi, u3elo0]
          · linarith only [h4, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
        · linarith only [h3, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
    · linarith only [h0, h1, hc15, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h12 | h12
    · linarith only [h0, h12, hc12, hlam, hphi, u1ehi4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h14 | h14
      · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
        · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
          · linarith only [h12, h16, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]
          · linarith only [h16, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
        · linarith only [h0, h15, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h14, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]

theorem r1l7_20_11_13_14_M_LI_L_R_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h3, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h0, h3, h4, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h6, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
            · linarith only [h5, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
          · linarith only [h4, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
        · linarith only [h3, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
        · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
          · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
            · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
              · linarith only [h17, h2, hc04, hlam, hphi, u4elo1]
              · linarith only [h17, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
            · linarith only [h16, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
          · linarith only [h15, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
        · linarith only [h14, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h24 | h24
    · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
      · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
        · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
          · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
            · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                  · linarith only [h24, h30, h31, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h25, h31, hc34, hlam, hphi, u4elo0]
                · linarith only [h27, h30, hc23, hlam, hphi, u3elo1]
              · linarith only [h29, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
            · linarith only [h28, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
          · linarith only [h27, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
        · linarith only [h26, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
        · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
          · rcases m.htr 1 3 5 (by decide) (by decide) with h41 | h41
            · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
              · linarith only [h25, h42, hc04, hlam, hphi, u4elo1]
              · linarith only [h42, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
            · linarith only [h40, h41, hlam, hphi, ht12, ht23, u1ehi3, u3elo4]
          · linarith only [h40, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
        · linarith only [h0, h24, h39, hlam]
    · linarith only [h0, h24, hlam, hphi, ht12, ht23, u1ehi0, u3elo2]

theorem r1l7_20_11_13_14_M_LI_L_R_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
      · linarith only [h2, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi2]
  · linarith only [h0, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_20_11_13_14_M_LI_L_R_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h2, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
            · linarith only [h5, hlam, hphi, ht34, u3ehi2, u4elo3]
          · linarith only [h4, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
        · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
            · linarith only [h0, h10, h12, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
            · linarith only [h12, h2, hc02, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h11, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
        · linarith only [h10, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
    · linarith only [h0, h1, hc15, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h18 | h18
    · linarith only [h0, h18, hc12, hlam, hphi, u1ehi4]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h20 | h20
      · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
        · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
          · linarith only [h18, h22, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
          · linarith only [h22, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
        · linarith only [h0, h21, hc24, hlam, hphi, ht12, u1ehi0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
        · rcases m.htr 1 4 5 (by decide) (by decide) with h27 | h27
          · linarith only [h18, h27, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
          · linarith only [h27, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
        · linarith only [h0, h26, hc24, hlam, hphi, ht12, u1ehi0]

theorem r1l7_20_11_13_14_M_LI_L_R_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · linarith only [h0, h2, h4, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
          · linarith only [h0, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · linarith only [h0, h2, h7, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10 | h10
        · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
          · linarith only [h0, h11, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
            · linarith only [h1, h13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
            · linarith only [h10, h13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
          · linarith only [h0, h16, h2, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
            · linarith only [h1, h10, h18, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
              · linarith only [h0, h10, h2, h20, hc23, hlam, hphi, ht12, u1ehi1]
              · linarith only [h0, h2, h20, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h24 | h24
    · linarith only [h0, h24, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h26 | h26
      · rcases m.htr 0 3 4 (by decide) (by decide) with h27 | h27
        · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
          · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
            · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
              · linarith only [h26, h30, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
              · linarith only [h26, h27, h30, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
            · linarith only [h24, h26, h27, h29, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
          · linarith only [h0, h28, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
          · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
            · linarith only [h24, h27, h36, hc13, hlam, hphi, u1ehi0]
            · linarith only [h24, h36, hc34, hlam, hphi, ht12, ht23, u1ehi0]
          · linarith only [h26, h35, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h40 | h40
        · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
          · linarith only [h0, h26, h41, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h41, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
          · linarith only [h0, h26, h44, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h44, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_20_11_13_14_M_LR_L_0_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
      · linarith only [h1, h2, hc13, hlam, hphi, u3elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo2]

theorem r1l7_20_11_13_14_M_LR_L_0_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h1, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
          · linarith only [h4, hlam, hphi, ht34, u3ehi2, u4elo3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
          · linarith only [h0, h1, h7, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
          · linarith only [h7, hlam, hphi, ht34, u3ehi2, u4elo3]
      · linarith only [h1, h2, hlam, hphi, ht34, u3ehi0, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h11 | h11
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
        · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
            · linarith only [h0, h12, h14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi4]
            · linarith only [h1, h11, h13, h14, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1, h13, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
          · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
            · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
              · linarith only [h1, h11, h12, h20, hc12, hc23, hlam, hphi]
              · linarith only [h18, h20, hlam, hphi, ht34, u3ehi3, u4elo4]
            · linarith only [h1, h19, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
          · linarith only [h1, h11, h18, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
      · linarith only [h11, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6, u4elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem r1l7_20_11_13_14_M_LR_L_0_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h4, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
          · linarith only [h2, h4, h6, hc34, hlam, hphi, u3ehi1]
          · linarith only [h2, h6, hc45, hlam, hphi, ht34, u3ehi1]
    · linarith only [h1, hlam, hphi, ht01, u0ehi5, u1elo3]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo2]

theorem r1l7_20_11_13_14_M_LR_L_I_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h1, h3, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
            · linarith only [h0, h1, h3, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
            · linarith only [h7, hlam, hphi, ht34, u3ehi1, u4elo3]
      · linarith only [h1, h2, hlam, hphi, ht34, u3ehi0, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h11 | h11
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
        · linarith only [h1, h11, h12, hc12, hlam, hphi, ht01, u0ehi8]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
              · linarith only [h0, h14, h16, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
              · linarith only [h1, h11, h15, h16, hc13, hlam, hphi, ht01, u0ehi8]
            · linarith only [h15, hlam, hphi, ht34, u3ehi1, u4elo3]
          · linarith only [h1, h11, h14, hc12, hc23, hlam, hphi]
      · linarith only [h11, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6, u4elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h22 | h22
    · rcases m.htr 0 2 4 (by decide) (by decide) with h23 | h23
      · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
        · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
          · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
            · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
              · linarith only [h22, h27, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
              · linarith only [h27, hlam, hphi, ht34, u3ehi2, u4elo3]
            · linarith only [h26, hlam, hphi, ht34, u3ehi1, u4elo3]
          · linarith only [h0, h23, h25, hlam, hphi, u0ehi5, u0elo1]
        · linarith only [h0, h24, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · linarith only [h22, h23, hlam, hphi, ht34, u3ehi0, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h34 | h34
      · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
        · linarith only [h0, h22, h35, hc12, hlam, hphi, ht01, u0ehi5]
        · linarith only [h0, h35, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · linarith only [h0, h34, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5, u4elo2]

theorem r1l7_20_11_13_14_M_LR_L_R_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h1, h3, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
        · linarith only [h0, h1, h2, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
    · linarith only [h1, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi5, u3elo1]

theorem r1l7_20_11_13_14_M_LR_L_R_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
    · linarith only [h1, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi5, u3elo1]

theorem r1l7_20_11_13_14_M_LR_L_R_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
        · linarith only [h0, h2, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
        · linarith only [h2, h6, hc12, hlam, hphi, ht01, u0ehi6]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
          · linarith only [h1, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
            · linarith only [h10, h6, h8, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h1, h10, h2, h6, hc35, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h14 | h14
    · linarith only [h0, h14, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h16 | h16
      · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
        · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
          · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
            · linarith only [h16, h19, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
              · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                · linarith only [h19, h22, hlam, hphi, ht34, u3ehi2, u4elo3]
                · linarith only [h21, h22, hc34, hlam, hphi, u4elo2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                · linarith only [h21, h25, hc24, hlam, hphi, u4elo3]
                · linarith only [h25, hlam, hphi, ht34, u3ehi3, u4elo4]
          · linarith only [h14, h18, hc35, hlam, hphi, ht12, ht23, u1ehi0]
        · linarith only [h0, h17, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
        · linarith only [h16, h30, hc12, hlam, hphi, ht01, u0ehi6]
        · linarith only [h0, h30, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem r1l7_20_11_13_H_I_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h3elo := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases h0emin with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, u1elo0]
        · linarith only [h0, h3, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, ht01, ht12, ht23, u3elo0]
        · linarith only [h1, h3, hlam, ht01, ht12, ht23, u3elo0]
        · linarith only [h2, h3, hlam, ht01, ht12, ht23, u3elo0]
      · rcases h0emin with h9 | h9 | h9 | h9 | h9
        · linarith only [h9, hlam, ht01, u1elo0]
        · linarith only [h0, h9, hlam, ht01, u1elo0]
        · linarith only [h2, h9, hlam, ht01, ht12, ht23, u3elo4]
        · linarith only [h1, h2, h9, hlam, ht01, ht12, ht23, u3elo4]
        · linarith only [h2, h9, hlam, ht01, ht12, ht23, u3elo4]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h15 | h15
      · rcases h0emin with h16 | h16 | h16 | h16 | h16
        · linarith only [h16, hlam, ht01, u1elo0]
        · linarith only [h0, h16, hlam, ht01, u1elo0]
        · linarith only [h1, h16, hlam, ht01, ht12, ht23, u3elo3]
        · linarith only [h1, h16, hlam, ht01, ht12, ht23, u3elo3]
        · linarith only [h1, h15, h16, hlam, ht01, ht12, ht23, u3elo3]
      · rcases h0emin with h22 | h22 | h22 | h22 | h22
        · linarith only [h22, hlam, ht01, u1elo0]
        · linarith only [h0, h22, hlam, ht01, u1elo0]
        · linarith only [h1, h22, hlam, ht01, ht12, ht23, u3elo3]
        · linarith only [h1, h22, hlam, ht01, ht12, ht23, u3elo3]
        · linarith only [h15, h22, hlam, ht01, ht12, ht23, u3elo4]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h28 | h28
    · rcases m.htr 0 3 5 (by decide) (by decide) with h29 | h29
      · rcases h0emin with h30 | h30 | h30 | h30 | h30
        · linarith only [h0, h30, hlam, ht01, u1elo1]
        · linarith only [h0, h30, hlam, ht01, u1elo1]
        · linarith only [h30, hlam, ht01, ht12, ht23, u3elo0]
        · linarith only [h28, h30, hlam, ht01, ht12, ht23, u3elo0]
        · linarith only [h29, h30, hlam, ht01, ht12, ht23, u3elo0]
      · rcases h0emin with h36 | h36 | h36 | h36 | h36
        · linarith only [h0, h36, hlam, ht01, u1elo1]
        · linarith only [h0, h36, hlam, ht01, u1elo1]
        · linarith only [h29, h36, hlam, ht01, ht12, ht23, u3elo4]
        · linarith only [h28, h29, h36, hlam, ht01, ht12, ht23, u3elo4]
        · linarith only [h29, h36, hlam, ht01, ht12, ht23, u3elo4]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h42 | h42
      · rcases h0emin with h43 | h43 | h43 | h43 | h43
        · linarith only [h0, h43, hlam, ht01, u1elo1]
        · linarith only [h0, h43, hlam, ht01, u1elo1]
        · linarith only [h28, h43, hlam, ht01, ht12, ht23, u3elo3]
        · linarith only [h28, h43, hlam, ht01, ht12, ht23, u3elo3]
        · linarith only [h28, h42, h43, hlam, ht01, ht12, ht23, u3elo3]
      · rcases h0emin with h49 | h49 | h49 | h49 | h49
        · linarith only [h0, h49, hlam, ht01, u1elo1]
        · linarith only [h0, h49, hlam, ht01, u1elo1]
        · linarith only [h28, h49, hlam, ht01, ht12, ht23, u3elo3]
        · linarith only [h28, h49, hlam, ht01, ht12, ht23, u3elo3]
        · linarith only [h42, h49, hlam, ht01, ht12, ht23, u3elo4]

theorem r1l7_20_11_13_H_L_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
    · linarith only [h2, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_20_11_13_H_L_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
      · linarith only [h2, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
        · linarith only [h0, h4, h6, hc13, hlam, hphi, u1ehi0]
        · linarith only [h0, h6, hc35, hlam, hphi, ht12, ht23, u1ehi0]

theorem r1l7_20_11_13_M_IR_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have h3elo := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases h0emin with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, u1elo0]
        · linarith only [h0, h3, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, ht01, ht12, ht23, u3elo0]
        · linarith only [h1, h3, hlam, ht01, u1elo0]
        · linarith only [h2, h3, hlam, ht01, ht12, ht23, u3elo0]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
    · linarith only [h1, hlam, hphi, ht01, u0ehi0, u1elo3]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem r1l7_20_11_13_M_LI_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h2, h5, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h0, h2, h3, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h3, h4, hlam, hphi, ht12, ht23, u1ehi3, u3elo4]
        · linarith only [h3, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
      · linarith only [h2, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
    · linarith only [h0, h12, hc12, hlam, hphi, u1ehi2]
    · linarith only [h12, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_20_11_13_M_LR_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h2, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
            · linarith only [h0, h2, h4, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h4, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
          · linarith only [h2, h3, h9, hlam]
          · linarith only [h9, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
      · linarith only [h2, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h14 | h14
    · linarith only [h0, h14, hc12, hlam, hphi, u1ehi2]
    · linarith only [h14, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_20_11_14_H_I_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h4elo := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases h0emin with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, u1elo0]
        · linarith only [h0, h3, hlam, ht01, u1elo0]
        · linarith only [h1, h3, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h2, h3, hlam, ht01, u1elo0]
      · rcases h0emin with h9 | h9 | h9 | h9 | h9
        · linarith only [h2, h9, hlam, ht01, u1elo4]
        · linarith only [h0, h2, h9, hlam, ht01, u1elo4]
        · linarith only [h1, h2, h9, hlam, ht01, u1elo4]
        · linarith only [h9, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h2, h9, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h15 | h15
      · rcases h0emin with h16 | h16 | h16 | h16 | h16
        · linarith only [h1, h16, hlam, ht01, u1elo2]
        · linarith only [h0, h1, h16, hlam, ht01, u1elo2]
        · linarith only [h1, h16, hlam, ht01, u1elo2]
        · linarith only [h16, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h1, h15, h16, hlam, ht01, u1elo2]
      · rcases h0emin with h22 | h22 | h22 | h22 | h22
        · linarith only [h1, h22, hlam, ht01, u1elo2]
        · linarith only [h0, h1, h22, hlam, ht01, u1elo2]
        · linarith only [h1, h22, hlam, ht01, u1elo2]
        · linarith only [h22, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h15, h22, hlam, ht01, u1elo4]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h28 | h28
    · rcases m.htr 0 1 5 (by decide) (by decide) with h29 | h29
      · rcases h0emin with h30 | h30 | h30 | h30 | h30
        · linarith only [h0, h30, hlam, ht01, u1elo1]
        · linarith only [h0, h30, hlam, ht01, u1elo1]
        · linarith only [h0, h28, h30, hlam, ht01, u1elo1]
        · linarith only [h30, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h0, h29, h30, hlam, ht01, u1elo1]
      · rcases h0emin with h36 | h36 | h36 | h36 | h36
        · linarith only [h0, h36, hlam, ht01, u1elo1]
        · linarith only [h0, h36, hlam, ht01, u1elo1]
        · linarith only [h0, h28, h36, hlam, ht01, u1elo1]
        · linarith only [h36, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h29, h36, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h42 | h42
      · rcases h0emin with h43 | h43 | h43 | h43 | h43
        · linarith only [h0, h43, hlam, ht01, u1elo1]
        · linarith only [h0, h43, hlam, ht01, u1elo1]
        · linarith only [h28, h43, hlam, ht01, u1elo2]
        · linarith only [h43, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h0, h42, h43, hlam, ht01, u1elo1]
      · rcases h0emin with h49 | h49 | h49 | h49 | h49
        · linarith only [h0, h49, hlam, ht01, u1elo1]
        · linarith only [h0, h49, hlam, ht01, u1elo1]
        · linarith only [h28, h49, hlam, ht01, u1elo2]
        · linarith only [h49, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h42, h49, hlam, ht01, u1elo4]

theorem r1l7_20_11_14_H_L_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
    · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem r1l7_20_11_14_H_L_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
      · linarith only [h4, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
        · linarith only [h0, h2, h4, h6, hc34, hlam, hphi, ht12, ht23, u1ehi0]
        · linarith only [h0, h2, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]

theorem r1l7_20_11_14_M_IR_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases h0emin with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, u1elo0]
        · linarith only [h0, h3, hlam, ht01, u1elo0]
        · linarith only [h1, h3, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, ht01, ht12, ht23, ht34, u4elo0]
        · linarith only [h2, h3, hlam, ht01, ht12, ht23, ht34, u4elo0]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
    · linarith only [h1, hlam, hphi, ht01, u0ehi0, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem r1l7_20_11_14_M_IR_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases h0bigk with h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc01, hlam, hphi, p9_1, u0ehi1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc01, hlam, hphi, p9_1, u0ehi2]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc01, hlam, hphi, p9_1, u0ehi3]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc01, hlam, hphi, p9_1, u0ehi4]
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
                      linarith only [h5, h6, hc02, hlam, hphi, p9_1, u0ehi4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h0, h6, hc01, hlam, hphi, p9_1, u0ehi4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h0, hc01, hlam, hphi, p9_1, u0ehi4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h1, hlam, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc03, hlam, hphi, p9_1, u0ehi1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h1, h6, hc01, hlam, hphi, p9_1, u0ehi4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, p9_1, u0ehi4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h2, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h4, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h5, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc04, hlam, hphi, p9_1, u0ehi4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h3, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc05, hlam, hphi, p9_1, u0ehi1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h6, hc03, hlam, hphi, ht34, p9_1, u4elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h6, hlam, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                  · linarith only [h8, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
              · linarith only [h6, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2, u4elo3]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h43 | h43
    · linarith only [h0, h43, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h45 | h45
      · linarith only [h0, h45, hc12, hlam, hphi, u1ehi3]
      · linarith only [h45, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem r1l7_20_11_14_M_LI_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h3, h6, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
              · linarith only [h0, h3, h5, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h5, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
          · linarith only [h4, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h14 | h14
    · linarith only [h0, h14, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h16 | h16
      · linarith only [h0, h16, hc12, hlam, hphi, u1ehi3]
      · linarith only [h16, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem r1l7_20_11_14_M_LR_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h2, h6, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
              · linarith only [h0, h2, h3, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h0, h2, h3, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
          · linarith only [h0, h2, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
    · linarith only [h1, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
    · linarith only [h0, h14, hc13, hlam, hphi, u1ehi3]
    · linarith only [h14, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem r1l7_20_11_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
        · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h4, h8, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
              · linarith only [h4, h5, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · linarith only [h2, h4, h5, h7, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi0]
          · linarith only [h0, h6, hc34, hlam, hphi, ht12, ht23, u1ehi0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
            · linarith only [h13, h14, h2, h5, hc13, hlam, hphi, u1ehi0]
            · linarith only [h14, h2, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
          · linarith only [h13, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
        · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
          · linarith only [h0, h19, h4, hc13, hlam, hphi, u1ehi0]
          · linarith only [h0, h19, hc34, hlam, hphi, ht12, ht23, u1ehi0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
          · linarith only [h0, h22, h4, hc13, hlam, hphi, u1ehi0]
          · linarith only [h0, h22, hc34, hlam, hphi, ht12, ht23, u1ehi0]

theorem r1l7_20_11_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem r1l7_20_11_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases h0emin with h4 | h4 | h4 | h4 | h4
          · linarith only [h4, hlam, ht01, u1elo0]
          · linarith only [h0, h4, hlam, ht01, u1elo0]
          · linarith only [h1, h4, hlam, ht01, u1elo0]
          · linarith only [h2, h4, hlam, ht01, u1elo0]
          · linarith only [h3, h4, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, hphi, ht01, u0ehi0, u1elo4]
      · linarith only [h0, h2, hlam, hphi, ht01, u0ehi1, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi1, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem r1l7_20_11_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem r1l7_20_12_13_15_H_L_L_0_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
        · linarith only [h5, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
          · linarith only [h0, h1, h3, h5, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · linarith only [h0, h1, h7, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h10 | h10
    · linarith only [h10, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h12 | h12
      · linarith only [h12, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h14 | h14
        · linarith only [h14, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
          · linarith only [h0, h12, h16, hc01, hlam, hphi, ht12, u2elo1]
          · linarith only [h0, h16, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_13_15_H_L_L_R_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
  · linarith only [h0, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_20_12_13_15_H_L_L_R_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
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
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
      · linarith only [h4, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
        · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
          · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h4, h8, hc24, hlam, hphi, u2ehi0]
            · linarith only [h0, h6, h7, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
          · linarith only [h0, h6, h7, hc45, hlam, hphi, ht23, ht34, u2ehi0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
          · linarith only [h0, h12, h4, h6, hc24, hlam, hphi, u2ehi0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
            · linarith only [h12, h14, h6, hc24, hlam, hphi, u2ehi1]
            · linarith only [h0, h14, hc45, hlam, hphi, ht23, ht34, u2ehi0]

theorem r1l7_20_12_13_15_H_R_L_R_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h0, h10, h5, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h13, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h0, h15, h5, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h13, h17, h5, h7, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h13, h17, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h0, h3, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
            · linarith only [h22, h4, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
              · linarith only [h0, h2, h24, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                      · linarith only [h0, h2, h27, h29, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · linarith only [h1, h26, h29, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h22, h26, h28, hlam]
                  · linarith only [h27, h4, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h0, h2, h22, h26, h34, h35, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                    · linarith only [h22, h35, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                  · linarith only [h34, h4, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h3, hc25, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h1, hc14, hlam, hphi, ht01, u0ehi0]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_12_13_15_M_IR_L_0_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases h0bigk with h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc01, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, h2, hc02, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, hphi, ht01, ht12, p3_1, u0ehi4, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, p3_1, u0ehi4, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, ht23, p3_1, u0ehi1, u3elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, hphi, ht01, ht12, ht23, p3_1, u0ehi4, u3elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, ht23, p3_1, u0ehi4, u3elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc04, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, hphi, ht01, ht12, ht23, p3_1, u0ehi1, u3elo0]
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
          linarith only [h1, hlam, hphi, ht01, ht12, ht23, p3_1, u0ehi4, u3elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc05, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p3_1, u0ehi1, u5elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, ht34, ht45, p3_1, u5elo0]
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
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_20_12_13_15_M_IR_L_0_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h1, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
          · linarith only [h0, h3, h4, hc23, hlam, hphi, u3elo0]
        · linarith only [h2, h3, hc13, hlam, hphi, u3elo0]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_20_12_13_15_M_IR_L_0_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases h0bigk with h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p3_1, u5ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc02, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, p3_1, u0ehi3, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, p3_1, u0ehi4, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, hphi, ht01, ht12, p3_1, u0ehi3, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, hphi, ht01, ht12, p3_1, u0ehi4, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc04, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hc04, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc04, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc04, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, h1, hc05, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, h2, hc01, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, hphi, ht01, ht12, p3_1, u0ehi3, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_20_12_13_15_M_IR_L_0_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi4]
    · linarith only [h1, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]

theorem r1l7_20_12_13_15_M_IR_L_0_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
          · linarith only [h2, h4, h6, hc34, hlam, hphi, u3ehi2]
          · linarith only [h2, h6, hc45, hlam, hphi, ht34, u3ehi2]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi1, u2elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]

theorem r1l7_20_12_13_15_M_IR_L_R_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0ehi := hb0.2.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h4, h6, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h4, h6, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h7, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
              · linarith only [h6, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · linarith only [h4, hlam, hphi, ht23, u2ehi1, u3elo2]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h16 | h16
        · linarith only [h0, h16, h2, hlam, hphi, ht23, u2ehi1, u3elo0]
        · linarith only [h16, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
    · linarith only [h0, h1, hlam, hphi, ht23, u2ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
    · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
      · rcases m.htr 0 3 4 (by decide) (by decide) with h22 | h22
        · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
          · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
            · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
              · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                  · linarith only [h0, h20, h23, h25, h27, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h20, h23, h25, h26, h27, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h26, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
              · linarith only [h25, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h0, h24, hc24, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h20, h22, h23, hc23, hlam, hphi, ht01, ht12, u0ehi3]
        · linarith only [h22, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h35 | h35
        · linarith only [h20, h21, h35, hlam]
        · linarith only [h35, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
    · linarith only [h20, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_20_12_13_15_M_IR_L_R_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h2, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · linarith only [h3, hlam, hphi, ht23, u2ehi2, u3elo4]
      · linarith only [h2, hlam, hphi, ht23, u2ehi1, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht23, u2ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h8 | h8
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
      · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
        · linarith only [h0, h10, h8, h9, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
        · linarith only [h10, hlam, hphi, ht23, u2ehi2, u3elo4]
      · linarith only [h0, h9, hc23, hlam, hphi, ht01, ht12, u0ehi0]
    · linarith only [h8, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_20_12_13_15_M_LI_L_0_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
            · linarith only [h3, h4, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
              · linarith only [h3, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h3, h4, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h10, h3, h4, hc23, hlam, hphi, u3elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
          · linarith only [h13, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
            · linarith only [h1, h15, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
              · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                · linarith only [h15, h18, h3, hc12, hlam, hphi, ht23, u3elo2]
                · linarith only [h18, h3, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h17, h3, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
        · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
          · linarith only [h0, h2, h23, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · linarith only [h0, h2, h23, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
          · linarith only [h1, h22, h26, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
          · linarith only [h1, h2, h22, h26, hc12, hlam, hphi, u2elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h30 | h30
    · rcases m.htr 0 1 5 (by decide) (by decide) with h31 | h31
      · linarith only [h0, h31, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
        · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
          · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
            · linarith only [h30, h31, h34, h35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
            · linarith only [h30, h31, h35, hc13, hlam, hphi, u3elo4]
          · linarith only [h0, h30, h33, h34, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
        · linarith only [h0, h30, h33, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h40 | h40
      · linarith only [h30, h40, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
        · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
          · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
            · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
              · rcases m.htr 2 3 5 (by decide) (by decide) with h46 | h46
                · linarith only [h42, h46, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                · linarith only [h44, h46, hc23, hlam, hphi, u3elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                · linarith only [h45, h49, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · linarith only [h44, h49, hc23, hlam, hphi, u3elo1]
            · linarith only [h30, h44, hc01, hlam, hphi, ht12, ht23, u3elo4]
          · linarith only [h0, h43, hc01, hlam, hphi, ht12, u2elo4]
        · linarith only [h0, h42, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_13_15_M_LI_L_R_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc24 := m.hcor 2 4 (by decide)
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
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h4, h6, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h0, h4, h5, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · linarith only [h5, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h4, hlam, hphi, ht23, u2ehi2, u3elo3]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
      · linarith only [h2, hlam, hphi, ht23, u2ehi1, u3elo2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_20_12_13_15_M_LI_L_R_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
      · linarith only [h2, hlam, hphi, ht23, u2ehi2, u3elo4]
    · linarith only [h1, hlam, hphi, ht23, u2ehi1, u3elo2]
  · linarith only [h0, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_20_12_13_15_M_LI_L_R_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
        · linarith only [h0, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
        · linarith only [h4, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h8 | h8
    · linarith only [h0, h8, hc23, hlam, hphi, u2ehi4]
    · linarith only [h8, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_20_12_13_15_M_LI_L_R_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
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
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
          · linarith only [h0, h2, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
          · linarith only [h0, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
          · linarith only [h0, h2, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10 | h10
        · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
          · linarith only [h0, h11, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
            · linarith only [h1, h13, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
            · linarith only [h10, h13, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
          · linarith only [h0, h16, h2, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
            · linarith only [h1, h10, h18, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
              · linarith only [h0, h10, h2, h20, hc34, hlam, hphi, ht23, u2ehi2]
              · linarith only [h0, h2, h20, hc45, hlam, hphi, ht23, ht34, u2ehi2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h24 | h24
    · linarith only [h0, h24, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h26 | h26
      · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
        · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
          · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
            · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
              · linarith only [h26, h30, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
              · linarith only [h26, h27, h30, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
            · linarith only [h24, h26, h27, h29, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
          · linarith only [h0, h28, hc34, hlam, hphi, ht23, u2ehi0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
          · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
            · linarith only [h24, h27, h36, hc24, hlam, hphi, u2ehi0]
            · linarith only [h24, h36, hc45, hlam, hphi, ht23, ht34, u2ehi0]
          · linarith only [h0, h26, h35, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3, u2ehi0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h40 | h40
        · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
          · linarith only [h0, h26, h41, hc23, hlam, hphi, u2ehi0]
          · linarith only [h0, h41, hc34, hlam, hphi, ht23, u2ehi0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
          · linarith only [h0, h26, h44, hc23, hlam, hphi, u2ehi0]
          · linarith only [h0, h44, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_20_12_13_15_M_LR_L_0_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h3, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
          · linarith only [h2, h4, hc23, hlam, hphi, u3elo0]
        · linarith only [h1, h3, hc12, hlam, hphi, u2elo0]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem r1l7_20_12_13_15_M_LR_L_0_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
      · linarith only [h1, h2, hc12, hlam, hphi, u2elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi6, u2elo4]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem r1l7_20_12_13_15_M_LR_L_0_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
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
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]

theorem r1l7_20_12_13_15_M_LR_L_0_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h2, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
        · linarith only [h0, h2, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
      · linarith only [h1, h2, hc12, hlam, hphi, u2elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi6, u2elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem r1l7_20_12_13_15_M_LR_L_I_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h1, h3, h5, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
            · linarith only [h0, h1, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h1, h9, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
              · linarith only [h3, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · linarith only [h1, h2, hlam, hphi, ht34, ht45, u3ehi0, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h13 | h13
      · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
        · linarith only [h1, h13, h14, hc12, hlam, hphi, ht01, u0ehi9]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
          · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
            · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
              · linarith only [h0, h16, h18, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
              · linarith only [h1, h13, h18, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
            · linarith only [h1, h13, h17, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
          · linarith only [h1, h13, h16, hc12, hc23, hlam, hphi]
      · linarith only [h13, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6, u5elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h24 | h24
    · rcases m.htr 0 2 5 (by decide) (by decide) with h25 | h25
      · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
        · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
          · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
            · linarith only [h24, h28, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
              · linarith only [h24, h30, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
              · linarith only [h30, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
          · linarith only [h0, h25, h27, hlam, hphi, u0ehi5, u0elo1]
        · linarith only [h0, h26, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · linarith only [h24, h25, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h36 | h36
      · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
        · linarith only [h0, h24, h37, hc12, hlam, hphi, ht01, u0ehi5]
        · linarith only [h0, h37, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · linarith only [h0, h36, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi5, u5elo2]

theorem r1l7_20_12_13_15_M_LR_L_R_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h7, h9, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h0, h7, h8, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h8, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                · linarith only [h7, hlam, hphi, ht23, u2ehi2, u3elo3]
              · linarith only [h1, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
            · linarith only [h5, hlam, hphi, ht23, u2ehi1, u3elo2]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi8, u5elo4]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
      · linarith only [h0, h2, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]

theorem r1l7_20_12_13_15_M_LR_L_R_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
        · linarith only [h3, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
      · linarith only [h2, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
    · linarith only [h0, h1, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
    · linarith only [h0, h8, hc12, hlam, hphi, ht01, u0ehi6]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
      · linarith only [h10, h8, hc23, hlam, hphi, u2ehi4]
      · linarith only [h10, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]

theorem r1l7_20_12_13_H_L_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
        · linarith only [h0, h1, h3, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
        · linarith only [h0, h1, h5, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h8 | h8
    · linarith only [h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h10 | h10
      · linarith only [h10, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
        · linarith only [h0, h10, h12, hc01, hlam, hphi, ht12, u2elo1]
        · linarith only [h0, h12, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_13_H_L_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
  · linarith only [h0, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_20_12_13_H_L_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
      · linarith only [h0, h2, h4, hc23, hlam, hphi, u2ehi0]
      · linarith only [h0, h4, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_20_12_13_M_IR_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3elo := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases h0bigk with h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c | h4c
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc01, hlam, hphi, p4_1, u0ehi1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h3, hc01, hlam, hphi, p4_1, u0ehi3]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc01, hlam, hphi, p4_1, u0ehi3]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc01, hlam, hphi, p4_1, u0ehi4]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h0, hlam, p4_1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h3, hc02, hlam, hphi, p4_1, u0ehi3]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, hphi, ht01, ht12, p4_1, u0ehi3, u2elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, hphi, ht01, ht12, p4_1, u0ehi4, u2elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc03, hlam, hphi, p4_1, u0ehi0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, hphi, ht01, ht12, ht23, p4_1, u0ehi3, u3elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, hphi, ht01, ht12, ht23, p4_1, u0ehi4, u3elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc04, hlam, hphi, p4_1, u0ehi0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h1, h3, hlam, p4_1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h3, hlam, p4_1]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h3, hlam, hphi, ht01, ht12, ht23, p4_1, u0ehi4, u3elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hc05, hlam, hphi, p4_1, u0ehi0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h2, hlam, p4_0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h0, h2, h3, hc01, hlam, hphi, p4_1, u0ehi3]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [h2, hlam, hphi, ht01, ht12, p4_1, u0ehi3, u2elo0]
          · have p4_0 := h4c.1
            have p4_1 := h4c.2.1
            have p4_2 := h4c.2.2.1
            have p4_3 := h4c.2.2.2
            linarith only [hlam, p4_0]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_20_12_13_M_IR_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem r1l7_20_12_13_M_LR_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h4, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h3, h7, hc23, hlam, hphi, u3elo0]
              · linarith only [h3, h6, hc13, hlam, hphi, u3elo0]
            · linarith only [h2, h5, hc12, hlam, hphi, u2elo0]
          · linarith only [h1, h4, hc12, hlam, hphi, u2elo0]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi6, u2elo3]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem r1l7_20_12_13_M_LR_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
      · linarith only [h1, h2, hc12, hlam, hphi, u2elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem r1l7_20_12_14_H_L_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
    · linarith only [h2, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]

theorem r1l7_20_12_14_H_L_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
      · linarith only [h4, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
        · linarith only [h6, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
          · linarith only [h0, h4, h8, hc23, hlam, hphi, u2ehi0]
          · linarith only [h0, h8, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_20_12_14_H_R_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h4, h6, h8, hc34, hlam, hphi, ht23, u2ehi2]
              · linarith only [h4, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
        · linarith only [h12, h2, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
          · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
            · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
              · linarith only [h0, h1, h14, h16, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h0, h1, h14, h15, h16, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · linarith only [h12, h15, hc45, hlam, hphi, ht23, ht34, u2ehi1]
          · linarith only [h14, h2, hc34, hlam, hphi, ht23, u2ehi1]
    · linarith only [h1, hc23, hlam, hphi, ht01, ht12, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_12_14_M_IR_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases h0bigk with h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c | h5c
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hlam, p5_0]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hc01, hlam, hphi, p5_1, u0ehi1]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hc01, hlam, hphi, p5_1, u0ehi2]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hc01, hlam, hphi, p5_1, u0ehi3]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hc01, hlam, hphi, p5_1, u0ehi4]
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
              linarith only [h3, hc02, hlam, hphi, p5_1, u0ehi3]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hlam, hphi, ht01, ht12, p5_1, u0ehi3, u2elo0]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hlam, hphi, ht01, ht12, p5_1, u0ehi4, u2elo0]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hc03, hlam, hphi, p5_1, u0ehi0]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hc03, hlam, hphi, p5_1, u0ehi1]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hlam, p5_0]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hc03, hlam, hphi, p5_1, u0ehi3]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hc03, hlam, hphi, p5_1, u0ehi4]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [h1, hlam, p5_0]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [h2, hlam, p5_0]
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
              linarith only [h2, hc02, hlam, hphi, p5_1, u0ehi4]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [h0, h4, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p5_1]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hc05, hlam, hphi, p5_1, u0ehi1]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hc05, hlam, hphi, p5_1, u0ehi2]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hc05, hlam, hphi, p5_1, u0ehi3]
            · have p5_0 := h5c.1
              have p5_1 := h5c.2.1
              have p5_2 := h5c.2.2.1
              have p5_3 := h5c.2.2.2
              linarith only [hlam, p5_0]
          · linarith only [h2, h4, hc12, hlam, hphi, u2elo0]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2, u4elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi1, u2elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo1]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_20_12_14_M_IR_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases h0bigk with h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi4]
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
          linarith only [hc02, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, p3_1, u0ehi3, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, p3_1, u0ehi4, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, p3_1, u0ehi0]
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
          linarith only [h1, hlam, hphi, ht01, ht12, p3_1, u0ehi3, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, hphi, ht01, ht12, p3_1, u0ehi4, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc04, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hc04, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc04, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc04, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, h1, hc05, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, h2, hc01, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, hphi, ht01, ht12, p3_1, u0ehi3, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_20_12_14_M_LI_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h3, h5, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
            · linarith only [h2, h5, hc34, hlam, hphi, u4elo1]
          · linarith only [h2, h4, hc24, hlam, hphi, u4elo1]
        · linarith only [h3, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
        · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
          · linarith only [h0, h10, h11, h2, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
          · linarith only [h11, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
        · linarith only [h10, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h16 | h16
    · linarith only [h0, h16, hc23, hlam, hphi, u2ehi3]
    · linarith only [h16, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]

theorem r1l7_20_12_14_M_LR_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2elo := hb2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h4, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                · linarith only [h0, h5, h8, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h1, h10, h3, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · linarith only [h10, h6, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
          · linarith only [h1, h4, hc12, hlam, hphi, u2elo0]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7, u4elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi6, u2elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem r1l7_20_12_14_M_LR_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
      · linarith only [h1, h2, hc12, hlam, hphi, u2elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi6, u2elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem r1l7_20_12_14_M_LR_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h4, h6, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h2, h6, hc34, hlam, hphi, u4elo0]
            · linarith only [h2, h5, hc24, hlam, hphi, u4elo0]
          · linarith only [h4, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
        · linarith only [h0, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h14 | h14
    · linarith only [h0, h14, hc23, hlam, hphi, u2ehi3]
    · linarith only [h14, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]

theorem r1l7_20_12_15_H_L_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
        · linarith only [h0, h1, h3, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
        · linarith only [h0, h1, h5, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h8 | h8
    · linarith only [h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h10 | h10
      · linarith only [h10, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
        · linarith only [h0, h10, h12, hc01, hlam, hphi, ht12, u2elo1]
        · linarith only [h0, h12, hc01, hlam, hphi, ht12, u2elo4]

theorem r1l7_20_12_15_H_L_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi4]
  · linarith only [h0, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_20_12_15_H_L_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h5ehi := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
      · linarith only [h4, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
        · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
          · linarith only [h2, h4, h7, hc24, hlam, hphi, u2ehi0]
          · linarith only [h2, h7, hc45, hlam, hphi, ht23, ht34, u2ehi0]
        · linarith only [h0, h6, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_20_12_15_M_IR_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 4 5 (by decide) (by decide) with h5 | h5
            · rcases h0bigk with h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc01, hlam, hphi, p6_1, u0ehi1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc01, hlam, hphi, p6_1, u0ehi2]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc01, hlam, hphi, p6_1, u0ehi3]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc01, hlam, hphi, p6_1, u0ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc02, hlam, hphi, p6_1, u0ehi0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc02, hlam, hphi, p6_1, u0ehi2]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc02, hlam, hphi, p6_1, u0ehi3]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc02, hlam, hphi, p6_1, u0ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc03, hlam, hphi, p6_1, u0ehi0]
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
                linarith only [h1, h2, hc02, hlam, hphi, p6_1, u0ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h1, hc02, hlam, hphi, p6_1, u0ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, h4, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6_1, u2ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc04, hlam, hphi, p6_1, u0ehi1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc04, hlam, hphi, p6_1, u0ehi2]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc04, hlam, hphi, p6_1, u0ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, hlam, p6_1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc05, hlam, hphi, p6_1, u0ehi1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p6_1, u0ehi2, u5elo0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h2, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
            · linarith only [h5, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h4, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
          · linarith only [h1, h3, h34, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
          · linarith only [h34, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h38 | h38
      · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
        · linarith only [h1, h39, hc12, hlam, hphi, ht01, u0ehi1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
          · linarith only [h39, h41, hc23, hlam, hphi, u2ehi4]
          · linarith only [h41, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
      · linarith only [h38, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo1]

theorem r1l7_20_12_15_M_LR_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
          · linarith only [h2, h3, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
        · linarith only [h1, h3, hc12, hlam, hphi, u2elo0]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi6, u2elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem r1l7_20_12_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  linarith only [hlam, hphi, ht01, ht12, u0ehi1, u2elo0]

theorem r1l7_20_12_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases h0bigk with h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc02, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, p3_1, u0ehi3, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, p3_1, u0ehi4, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, hphi, ht01, ht12, p3_1, u0ehi3, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, hphi, ht01, ht12, p3_1, u0ehi4, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc04, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hc04, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc04, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc04, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, h1, hc05, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, h2, hc01, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, hphi, ht01, ht12, p3_1, u0ehi3, u2elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_20_13_14_H_L_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
        · linarith only [h4, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
        · linarith only [h0, h1, h3, h4, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
        · linarith only [h7, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
          · linarith only [h0, h1, h7, h9, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi3]
          · linarith only [h0, h1, h9, hc23, hlam, hphi, u3elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h12 | h12
    · linarith only [h12, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14 | h14
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15 | h15
        · linarith only [h15, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
          · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
            · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
              · linarith only [h12, h15, h17, h19, hc02, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                · linarith only [h17, h19, h21, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
                · linarith only [h14, h21, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · linarith only [h14, h18, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
          · linarith only [h0, h17, hc02, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
        · linarith only [h26, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
          · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
            · linarith only [h14, h29, hc03, hlam, hphi, u3elo2]
            · linarith only [h0, h29, hc02, hlam, hphi, ht23, u3elo4]
          · linarith only [h0, h28, hc02, hlam, hphi, ht23, u3elo3]

theorem r1l7_20_13_14_H_L_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
  · linarith only [h0, hlam, hphi, ht34, u3ehi0, u4elo3]

theorem r1l7_20_13_14_H_L_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
      · linarith only [h0, h2, h4, hc34, hlam, hphi, u3ehi0]
      · linarith only [h0, h4, hc45, hlam, hphi, ht34, u3ehi0]

theorem r1l7_20_13_14_M_IR_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h3elo := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases h0bigk with h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc01, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc02, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc02, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc02, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc02, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, ht23, p3_1, u0ehi4, u3elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc04, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc02, hlam, hphi, ht23, p3_1, u3elo0]
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
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, hphi, ht01, ht12, ht23, p3_1, u0ehi4, u3elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc05, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hc02, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hc02, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h30 | h30
      · rcases h0bigk with h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c | h31c
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hlam, p31_0]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hc01, hlam, hphi, p31_1, u0ehi1]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [h30, hc01, hlam, hphi, p31_1, u0ehi3]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hc01, hlam, hphi, p31_1, u0ehi3]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hc01, hlam, hphi, p31_1, u0ehi4]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hc02, hlam, hphi, p31_1, u0ehi0]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hlam, p31_0]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [h1, hc05, hlam, hphi, p31_1, u0ehi2]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [h1, hc25, hlam, hphi, ht01, ht12, p31_1, u0ehi3]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [h1, hlam, p31_0]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hc03, hlam, hphi, p31_1, u0ehi0]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [h0, hlam, p31_1]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hlam, p31_0]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hc03, hlam, hphi, p31_1, u0ehi3]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, ht23, p31_1, u0ehi4, u3elo0]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hc04, hlam, hphi, p31_1, u0ehi0]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [h30, hc02, hlam, hphi, ht23, p31_1, u3elo0]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [h30, hlam, p31_0]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hlam, p31_0]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [h0, h1, h30, hlam, p31_1]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hc05, hlam, hphi, p31_1, u0ehi0]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hc05, hlam, hphi, p31_1, u0ehi1]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [h1, h30, hc25, hlam, hphi, ht01, ht12, p31_1, u0ehi3]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [h1, hc25, hlam, hphi, ht01, ht12, p31_1, u0ehi3]
        · have p31_0 := h31c.1
          have p31_1 := h31c.2.1
          have p31_2 := h31c.2.2.1
          have p31_3 := h31c.2.2.2
          linarith only [hlam, p31_0]
      · linarith only [h30, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]

theorem r1l7_20_13_14_M_LR_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h5, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h3, h6, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
              · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, h2, h9, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h10, h4, hc34, hlam, hphi, u4elo0]
              · linarith only [h3, h5, h9, hc13, hlam, hphi, u3elo0]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi5, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h18 | h18
    · rcases m.htr 0 2 3 (by decide) (by decide) with h19 | h19
      · rcases m.htr 0 3 4 (by decide) (by decide) with h20 | h20
        · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
          · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
            · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
              · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                · linarith only [h18, h22, h23, h24, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h21, h24, hc34, hlam, hphi, u4elo0]
              · linarith only [h20, h23, hc23, hlam, hphi, u3elo0]
            · linarith only [h0, h22, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h21, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
        · linarith only [h20, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
      · linarith only [h19, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]
    · linarith only [h18, hlam, hphi, ht01, ht12, ht23, u0ehi5, u3elo1]

theorem r1l7_20_13_14_M_LR_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
      · linarith only [h1, h2, hc23, hlam, hphi, u3elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]

theorem r1l7_20_13_15_H_L_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
        · linarith only [h0, h1, h4, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
          · linarith only [h0, h1, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
          · linarith only [h3, h4, h6, hc13, hlam, hphi, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h9 | h9
        · linarith only [h9, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
          · linarith only [h11, h3, hc03, hlam, hphi, u3elo1]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
            · linarith only [h0, h1, h13, h9, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
            · linarith only [h0, h1, h13, hc13, hlam, hphi, u3elo4]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h16 | h16
    · linarith only [h16, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h18 | h18
      · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
        · linarith only [h19, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
          · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
            · linarith only [h0, h19, h22, hc01, hlam, hphi, ht12, ht23, u3elo1]
            · linarith only [h0, h22, hc01, hlam, hphi, ht12, ht23, u3elo4]
          · linarith only [h0, h18, h21, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h26 | h26
        · linarith only [h18, h26, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
          · linarith only [h18, h28, hc03, hlam, hphi, u3elo1]
          · linarith only [h0, h28, hc01, hlam, hphi, ht12, ht23, u3elo3]

theorem r1l7_20_13_15_H_L_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
  · linarith only [h0, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem r1l7_20_13_15_M_LR_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
      · linarith only [h1, h2, hc23, hlam, hphi, u3elo0]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]

theorem r1l7_20_13_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.1
  have h3elo := hb3.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo0]

theorem r1l7_20_13_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h3elo := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases h0bigk with h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc02, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc02, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc02, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc02, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, hphi, ht01, ht12, ht23, p3_1, u0ehi4, u3elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc04, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc02, hlam, hphi, ht23, p3_1, u3elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, hphi, ht01, ht12, ht23, p3_1, u0ehi4, u3elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc05, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc05, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc05, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc05, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_20_14_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.1
  have h4elo := hb4.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo0]

theorem r1l7_20_14_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases h0bigk with h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi3]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc02, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc02, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc02, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc02, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc03, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc01, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc01, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc05, hlam, hphi, p3_1, u0ehi0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, p3_1, u0ehi1, u4elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc03, hlam, hphi, ht34, p3_1, u4elo0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2, u4elo3]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]

theorem r1l7_20_14_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem r1l7_20_15_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h5elo := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem r1l7_20_15_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · rcases h0bigk with h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc01, hlam, hphi, p2_1, u0ehi1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc01, hlam, hphi, p2_1, u0ehi2]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc01, hlam, hphi, p2_1, u0ehi3]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc01, hlam, hphi, p2_1, u0ehi4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hlam, p2_1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc02, hlam, hphi, p2_1, u0ehi2]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, h1, hc01, hlam, hphi, p2_1, u0ehi4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hc01, hlam, hphi, p2_1, u0ehi4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc03, hlam, hphi, p2_1, u0ehi0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc03, hlam, hphi, p2_1, u0ehi1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h1, hc03, hlam, hphi, p2_1, u0ehi4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc03, hlam, hphi, p2_1, u0ehi4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hc04, hlam, hphi, p2_1, u0ehi1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc04, hlam, hphi, p2_1, u0ehi1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc04, hlam, hphi, p2_1, u0ehi2]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc04, hlam, hphi, p2_1, u0ehi4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hc05, hlam, hphi, p2_1, u0ehi1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p2_1, u0ehi1, u5elo0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p2_1, u0ehi2, u5elo0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h1, hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h29 | h29
    · rcases h0bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hlam, p30_0]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [h0, hlam, p30_0]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hc01, hlam, hphi, p30_1, u0ehi2]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [h0, h29, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p30_1]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p30_1, u0ehi4]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p30_1, u0ehi0]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hlam, p30_0]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p30_1, u0ehi2]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [h0, h29, hc12, hlam, hphi, ht01, p30_1, u0ehi4]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [h0, hc12, hlam, hphi, ht01, p30_1, u0ehi4]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hc03, hlam, hphi, p30_1, u0ehi0]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hc03, hlam, hphi, p30_1, u0ehi1]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hlam, p30_0]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [h29, hc03, hlam, hphi, p30_1, u0ehi4]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hc03, hlam, hphi, p30_1, u0ehi4]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hc04, hlam, hphi, p30_1, u0ehi0]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [h0, hc04, hlam, hphi, p30_1, u0ehi0]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hc04, hlam, hphi, p30_1, u0ehi2]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hlam, p30_0]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hc04, hlam, hphi, p30_1, u0ehi4]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hc05, hlam, hphi, p30_1, u0ehi0]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [h0, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p30_1, u0ehi0, u5elo0]
      · have p30_0 := h30c.1
        have p30_1 := h30c.2.1
        have p30_2 := h30c.2.2.1
        have p30_3 := h30c.2.2.2
        linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, p30_1, u0ehi2, u5elo0]
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
    · linarith only [h29, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]

theorem r1l7_20_M_IR (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases h0bigk with h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc01, hlam, hphi, p1_1, u0ehi1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc01, hlam, hphi, p1_1, u0ehi2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc01, hlam, hphi, p1_1, u0ehi3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc01, hlam, hphi, p1_1, u0ehi4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc02, hlam, hphi, p1_1, u0ehi0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc02, hlam, hphi, p1_1, u0ehi2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc02, hlam, hphi, p1_1, u0ehi3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc02, hlam, hphi, p1_1, u0ehi4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc03, hlam, hphi, p1_1, u0ehi0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hlam, p1_1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc02, hlam, hphi, p1_1, u0ehi3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc02, hlam, hphi, p1_1, u0ehi4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc04, hlam, hphi, p1_1, u0ehi0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc04, hlam, hphi, p1_1, u0ehi1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc04, hlam, hphi, p1_1, u0ehi2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc04, hlam, hphi, p1_1, u0ehi4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u0ehi0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc05, hlam, hphi, p1_1, u0ehi2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u0ehi2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u0ehi3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
  · rcases h0bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc01, hlam, hphi, p27_1, u0ehi1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc01, hlam, hphi, p27_1, u0ehi1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc01, hlam, hphi, p27_1, u0ehi3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc01, hlam, hphi, p27_1, u0ehi4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p27_1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc23, hlam, hphi, ht01, ht12, p27_1, u0ehi3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc23, hlam, hphi, ht01, ht12, p27_1, u0ehi4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc03, hlam, hphi, p27_1, u0ehi0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc03, hlam, hphi, p27_1, u0ehi1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc23, hlam, hphi, ht01, ht12, p27_1, u0ehi3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc23, hlam, hphi, ht01, ht12, p27_1, u0ehi4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc04, hlam, hphi, p27_1, u0ehi0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc04, hlam, hphi, p27_1, u0ehi1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc04, hlam, hphi, p27_1, u0ehi2]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc04, hlam, hphi, p27_1, u0ehi4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u0ehi0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u0ehi1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc05, hlam, hphi, p27_1, u0ehi1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u0ehi3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]

theorem r1l7_21_14_H_L_L_0 (m : N7Model)
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4elo := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
            · linarith only [h1, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                · linarith only [h1, h10, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h10, h12, h5, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h12, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                · linarith only [h1, h15, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h15, h17, h3, h9, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h17, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · linarith only [h2, hc01, hlam, hphi, u1elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem r1l7_21_14_H_L_L_R (m : N7Model)
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
  · linarith only [h0, hc01, hlam, hphi, u1elo3]

theorem r1l7_21_14_H_R_L_0 (m : N7Model)
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo1]

theorem r1l7_21_14_H_R_L_R (m : N7Model)
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h1, h2, h4, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht45, ht5b, u1ehi4, u4ehi4]
                · linarith only [h0, h2, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h0, h3, h5, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
              · linarith only [h0, h11, h2, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                · linarith only [h0, h13, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h0, h13, h2, h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
        · linarith only [h3, hc35, hlam, hphi, ht12, ht23, u1ehi2]
      · linarith only [h2, hc34, hlam, hphi, ht12, ht23, u1ehi2]
    · linarith only [h1, hc23, hlam, hphi, ht12, u1ehi1]
  · linarith only [h0, hc13, hlam, hphi, u1ehi0]

theorem r1l7_21_15_H_L_L_0 (m : N7Model)
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h4, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h4, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
              · linarith only [h13, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                · linarith only [h1, h15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h15, h17, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h1, h12, h17, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
              · linarith only [h0, h20, h4, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
                · linarith only [h1, h22, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                  · linarith only [h12, h2, h22, h24, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h2, h26, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                          · linarith only [h20, h22, h26, h28, h30, hc12, hc23, hlam, hphi]
                          · linarith only [h20, h22, h30, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h29, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                        · linarith only [h0, h12, h28, h34, h4, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h34, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h3, hc01, hlam, hphi, u1elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem r1l7_21_15_H_L_L_R (m : N7Model)
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h1elo := hb1.1
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
  · linarith only [h0, hc01, hlam, hphi, u1elo4]

theorem r1l7_21_15_H_R_L_0 (m : N7Model)
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h5elo := hb5.1
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo1]

theorem r1l7_21_15_H_R_L_R (m : N7Model)
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h1, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
              · linarith only [h0, h1, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · linarith only [h0, h1, h2, h3, h4, h5, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
            · linarith only [h0, h1, h10, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
              · linarith only [h0, h1, h12, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · linarith only [h0, h1, h12, h2, h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h3, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
      · linarith only [h2, hc34, hlam, hphi, ht12, ht23, u1ehi2]
    · linarith only [h1, hc23, hlam, hphi, ht12, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem r1l7_21_M_LR (m : N7Model)
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi7 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi7, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo2]

theorem r1l7_22_13_15_H_L_L_0_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
          · linarith only [h2, h4, h6, hc23, hlam, hphi, u3elo3]
          · linarith only [h2, h6, hc23, hlam, hphi, ht34, ht45, u5elo4]
    · linarith only [h1, hc02, hlam, hphi, u2elo3]
  · linarith only [h0, hc02, hlam, hphi, u2elo2]

theorem r1l7_22_13_15_H_L_L_R_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
    · linarith only [h2, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]

theorem r1l7_22_13_15_H_R_L_R_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
      · linarith only [h2, hc25, hlam, hphi, u2ehi1]
    · linarith only [h1, hc23, hlam, hphi, u2ehi0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6 | h6
    · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
      · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
        · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
            · linarith only [h10, h6, h8, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
            · linarith only [h0, h10, h6, h8, h9, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h9, hc45, hlam, hphi, ht23, ht34, u2ehi3]
        · linarith only [h8, hc34, hlam, hphi, ht23, u2ehi2]
      · linarith only [h0, h7, hc25, hlam, hphi, u2ehi0]
    · linarith only [h6, hc23, hlam, hphi, u2ehi0]

theorem r1l7_22_13_H_L_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
  · linarith only [h0, hc12, hlam, hphi, u2elo2]

theorem r1l7_22_13_H_R_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  linarith only [hlam, hphi, ht23, u2ehi2, u3elo2]

theorem r1l7_22_14_H_L_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4elo := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
          · linarith only [h2, h4, h6, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h2, h6, hc23, hlam, hphi, ht34, u4elo4]
    · linarith only [h1, hc02, hlam, hphi, u2elo3]
  · linarith only [h0, hc02, hlam, hphi, u2elo2]

theorem r1l7_22_14_H_L_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
      · linarith only [h0, h1, h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
    · linarith only [h1, hc12, hlam, hphi, u2elo4]
  · linarith only [h0, hc01, hlam, hphi, ht12, u2elo1]

theorem r1l7_22_14_H_R_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  linarith only [hlam, hphi, ht23, ht34, u2ehi3, u4elo2]

theorem r1l7_22_14_H_R_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
          · linarith only [h0, h2, h3, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
        · linarith only [h3, hc45, hlam, hphi, ht23, ht34, u2ehi3]
      · linarith only [h2, hc34, hlam, hphi, ht23, u2ehi2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, hc23, hlam, hphi, u2ehi1]

theorem r1l7_22_14_M_LR_L_0 (m : N7Model)
    (hb2 : CMSig2_7_M_LR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h2elo := hb2.1
  have h2ehi := hb2.2.2.1
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u2ehi6 := h2ehi (m.d 1 2) (by simp)
  have u2ehi9 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u2ehi9, u2elo1]
  · linarith only [h0, hlam, hphi, u2ehi6, u2elo4]

theorem r1l7_22_15_H_L_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
  · linarith only [h0, hc02, hlam, hphi, u2elo4]

theorem r1l7_22_15_H_R_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  linarith only [hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo2]

theorem r1l7_22_M_LR (m : N7Model)
    (hb2 : CMSig2_7_M_LR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h2elo := hb2.1
  have h2ehi := hb2.2.2.1
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2ehi6 := h2ehi (m.d 1 2) (by simp)
  have u2ehi8 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u2ehi8, u2elo1]
  · linarith only [h0, hlam, hphi, u2ehi6, u2elo3]

theorem r1l7_23_M_LR (m : N7Model)
    (hb3 : CMSig2_7_M_LR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h3elo := hb3.1
  have h3ehi := hb3.2.2.1
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3ehi7 := h3ehi (m.d 2 3) (by simp)
  have u3ehi8 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u3ehi8, u3elo2]
  · linarith only [h0, hlam, hphi, u3ehi7, u3elo3]

theorem r1l7_24_M_LR (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem r1l7_25_M_LI (m : N7Model)
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · rcases h5bigk with h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc15, hlam, hphi, p1_1, u5elo0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc25, hlam, hphi, p1_1, u5elo0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc35, hlam, hphi, p1_1, u5elo0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u5elo0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u5elo1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc45, hlam, hphi, p1_1, u5elo1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc35, hlam, hphi, p1_1, u5elo1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u5elo1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc15, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc35, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u5elo3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc15, hlam, hphi, p1_1, u5elo3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc25, hlam, hphi, p1_1, u5elo3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u5elo3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc05, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc15, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc35, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
  · rcases h5bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc15, hlam, hphi, p27_1, u5elo0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc25, hlam, hphi, p27_1, u5elo0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc35, hlam, hphi, p27_1, u5elo0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc45, hlam, hphi, p27_1, u5elo0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u5elo1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc24, hlam, hphi, ht45, p27_1, u5elo1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc35, hlam, hphi, p27_1, u5elo1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc24, hlam, hphi, ht45, p27_1, u5elo1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u5elo2]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc15, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc35, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hlam, p27_1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u5elo3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc15, hlam, hphi, p27_1, u5elo3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc25, hlam, hphi, p27_1, u5elo3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc45, hlam, hphi, p27_1, u5elo3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc15, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc24, hlam, hphi, ht45, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc35, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]

end R2N4
