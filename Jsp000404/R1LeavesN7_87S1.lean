import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


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

end R2N4
