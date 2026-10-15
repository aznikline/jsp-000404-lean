import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


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

end R2N4
