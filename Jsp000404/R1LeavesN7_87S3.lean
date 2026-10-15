import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


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

end R2N4
