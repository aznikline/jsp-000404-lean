import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAA3_H_I_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h3elo := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases h0emin with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, u1elo0]
        · linarith only [h0, h3, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, ht01, ht12, ht23, u3elo0]
        · linarith only [h1, h3, hlam, ht01, u1elo0]
        · linarith only [h2, h3, hlam, ht01, u1elo0]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA3_H_I_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
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
        · linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA3_H_I_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
  · linarith only [h0, hc01, hlam, hphi, u1elo2]

theorem n7l_sAA3_H_I_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAA3_H_I_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
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
                            linarith only [h0, h11, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, h11, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h11, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, h11, h9, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h11, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
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
                            linarith only [h4, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h11, h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h2, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h11, h8, h9, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h5, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h3, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h3, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h11, h8, h9, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p12_1, u1ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h6, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h7, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                        · linarith only [h0, h11, h4, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                      · linarith only [h10, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                    · linarith only [h9, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                  · linarith only [h8, hc23, hlam, hphi, ht12, u1ehi1]
                · linarith only [h2, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
              · linarith only [h1, h6, hc35, hlam, hphi, ht12, ht23, u1ehi2]
            · linarith only [h1, h5, hc34, hlam, hphi, ht12, ht23, u1ehi2]
          · linarith only [h0, h4, hc23, hlam, hphi, ht12, u1ehi1]
        · linarith only [h3, hc15, hlam, hphi, u1ehi0]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA3_H_I_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h1, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
        · linarith only [h0, h1, h2, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
      · linarith only [h2, hc35, hlam, hphi, ht12, ht23, u1ehi2]
    · linarith only [h1, hc23, hlam, hphi, ht12, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA3_H_I_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.2.1
  have h3elo := hb3.1
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
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases h0bigk with h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  rcases p7_3 (m.d 0 1) (by simp) with h11 | h11
                  · rcases p7_3 (m.d 0 2) (by simp) with h12 | h12
                    · linarith only [h0, h12, hlam]
                    · linarith only [h12, h2, h3, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p7_1, u1ehi4]
                  · linarith only [h11, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p7_1, u1ehi4]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, h5, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p7_1, u1ehi4]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  rcases p7_3 (m.d 0 1) (by simp) with h20 | h20
                  · rcases p7_3 (m.d 0 2) (by simp) with h21 | h21
                    · rcases p7_3 (m.d 0 3) (by simp) with h22 | h22
                      · linarith only [h22, h3, hlam]
                      · linarith only [h22, h4, hlam]
                    · linarith only [h21, hlam, p7_0]
                  · linarith only [h0, h20, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p7_1, u1ehi4]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h1, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h3, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, hlam, hphi, ht12, ht23, p7_1, u1ehi4, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p7_1, u1ehi0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h4, hc02, hlam, hphi, ht23, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h4, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, h4, hlam, hphi, ht12, ht23, p7_1, u1ehi4, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h3, h5, hc05, hc35, hlam, hphi, ht0b, ht5b, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h5, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
              · linarith only [h6, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
            · linarith only [h1, h5, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
          · linarith only [h1, h4, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
        · linarith only [h0, h3, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h49 | h49
    · linarith only [h0, h49, hc12, hlam, hphi, u1ehi2]
    · linarith only [h49, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem n7l_sAA3_H_I_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, u1elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, ht01, u1elo0]
    · linarith only [h0, h2, hlam, ht01, u1elo1]
  · linarith only [h0, hlam, ht01, ht12, ht23, u3elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 1 4 (by decide) (by decide) with h7 | h7
      · linarith only [h0, h7, hlam, ht01, u1elo0]
      · linarith only [h0, h7, hlam, ht01, u1elo3]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h10 | h10
      · linarith only [h0, h10, h6, hlam, ht01, u1elo1]
      · linarith only [h0, h10, hlam, ht01, u1elo3]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h13 | h13
    · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
      · rcases m.htr 0 3 5 (by decide) (by decide) with h15 | h15
        · linarith only [h0, h15, hlam, ht01, ht12, ht23, u3elo0]
        · linarith only [h0, h15, hlam, ht01, ht12, ht23, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h18 | h18
        · linarith only [h0, h18, hlam, ht01, ht12, ht23, u3elo0]
        · linarith only [h0, h18, hlam, ht01, ht12, ht23, u3elo4]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
      · rcases m.htr 0 3 5 (by decide) (by decide) with h22 | h22
        · linarith only [h0, h22, hlam, ht01, ht12, ht23, u3elo0]
        · linarith only [h0, h22, hlam, ht01, ht12, ht23, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h25 | h25
        · linarith only [h0, h25, hlam, ht01, ht12, ht23, u3elo0]
        · linarith only [h0, h25, hlam, ht01, ht12, ht23, u3elo4]

theorem n7l_sAA3_H_I_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, u1elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, ht01, u1elo0]
    · linarith only [h0, h2, hlam, ht01, u1elo1]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 1 3 (by decide) (by decide) with h6 | h6
      · linarith only [h0, h6, hlam, ht01, u1elo0]
      · linarith only [h0, h6, hlam, ht01, u1elo2]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
      · linarith only [h0, h5, h9, hlam, ht01, u1elo1]
      · linarith only [h0, h9, hlam, ht01, u1elo2]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
    · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
        · linarith only [h0, h14, hlam, ht01, u1elo0]
        · linarith only [h0, h14, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h13, h17, hlam, ht01, u1elo2]
        · linarith only [h0, h17, hlam, ht01, u1elo3]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
      · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
        · linarith only [h0, h12, h21, hlam, ht01, u1elo1]
        · linarith only [h0, h21, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h24 | h24
        · linarith only [h0, h12, h24, hlam, ht01, u1elo1]
        · linarith only [h0, h24, hlam, ht01, u1elo3]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h27 | h27
    · rcases m.htr 0 1 3 (by decide) (by decide) with h28 | h28
      · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
        · rcases m.htr 0 1 5 (by decide) (by decide) with h30 | h30
          · linarith only [h0, h30, hlam, ht01, u1elo0]
          · linarith only [h0, h30, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h33 | h33
          · linarith only [h0, h29, h33, hlam, ht01, u1elo3]
          · linarith only [h0, h33, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h36 | h36
        · rcases m.htr 0 1 5 (by decide) (by decide) with h37 | h37
          · linarith only [h0, h28, h37, hlam, ht01, u1elo2]
          · linarith only [h0, h37, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h40 | h40
          · linarith only [h0, h28, h40, hlam, ht01, u1elo2]
          · linarith only [h0, h40, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h43 | h43
      · rcases m.htr 0 1 4 (by decide) (by decide) with h44 | h44
        · rcases m.htr 0 1 5 (by decide) (by decide) with h45 | h45
          · linarith only [h0, h27, h45, hlam, ht01, u1elo1]
          · linarith only [h0, h45, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h48 | h48
          · linarith only [h0, h27, h48, hlam, ht01, u1elo1]
          · linarith only [h0, h48, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h51 | h51
        · rcases m.htr 0 1 5 (by decide) (by decide) with h52 | h52
          · linarith only [h0, h27, h52, hlam, ht01, u1elo1]
          · linarith only [h0, h52, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h55 | h55
          · linarith only [h0, h27, h55, hlam, ht01, u1elo1]
          · linarith only [h0, h55, hlam, ht01, u1elo4]

theorem n7l_sAA3_H_I_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, u1elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, ht01, u1elo0]
    · linarith only [h0, h2, hlam, ht01, u1elo1]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 1 3 (by decide) (by decide) with h6 | h6
      · linarith only [h0, h6, hlam, ht01, u1elo0]
      · linarith only [h0, h6, hlam, ht01, u1elo2]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
      · linarith only [h5, h9, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
      · linarith only [h0, h9, hlam, ht01, u1elo2]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
    · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
        · linarith only [h0, h14, hlam, ht01, u1elo0]
        · linarith only [h13, h14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h13, h17, hlam, ht01, u1elo2]
        · linarith only [h0, h17, hlam, ht01, u1elo3]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h20 | h20
      · linarith only [h12, h20, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h22 | h22
        · linarith only [h0, h12, h22, hlam, ht01, u1elo1]
        · linarith only [h0, h22, hlam, ht01, u1elo3]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h25 | h25
    · rcases m.htr 0 1 3 (by decide) (by decide) with h26 | h26
      · rcases m.htr 0 1 4 (by decide) (by decide) with h27 | h27
        · rcases m.htr 0 1 5 (by decide) (by decide) with h28 | h28
          · linarith only [h0, h28, hlam, ht01, u1elo0]
          · linarith only [h26, h28, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi1]
        · linarith only [h26, h27, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h32 | h32
        · rcases m.htr 0 1 5 (by decide) (by decide) with h33 | h33
          · linarith only [h0, h26, h33, hlam, ht01, u1elo2]
          · linarith only [h0, h33, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h36 | h36
          · linarith only [h0, h26, h36, hlam, ht01, u1elo2]
          · linarith only [h0, h36, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h39 | h39
      · linarith only [h25, h39, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h41 | h41
        · rcases m.htr 0 1 5 (by decide) (by decide) with h42 | h42
          · linarith only [h0, h25, h42, hlam, ht01, u1elo1]
          · linarith only [h0, h42, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h45 | h45
          · linarith only [h0, h25, h45, hlam, ht01, u1elo1]
          · linarith only [h0, h45, hlam, ht01, u1elo4]

theorem n7l_sAA3_H_I_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAA3_H_I_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA3_H_I_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA3_H_L_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h26 | h26
    · linarith only [h26, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h26, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h30 | h30
    · linarith only [h30, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h30, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h34, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_H_L_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_H_L_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h9 | h9
    · linarith only [h9, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h9, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h12 | h12
    · linarith only [h12, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h12, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h16 | h16
    · linarith only [h16, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h16, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · linarith only [h20, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h20, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h27 | h27
    · linarith only [h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h27, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_H_L_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3elo := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h2, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
          · linarith only [h1, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
            · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
              · linarith only [h2, h6, h9, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h2, h9, hc12, hlam, hphi, ht23, u3elo4]
            · linarith only [h2, h8, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h1, hc01, hlam, hphi, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA3_H_L_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h0, h2, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h0, h2, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
            · linarith only [h0, h12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h0, h12, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
            · linarith only [h0, h15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h0, h15, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h18 | h18
        · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
            · linarith only [h2, h20, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
              · linarith only [h1, h22, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1, h18, h22, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
            · linarith only [h0, h18, h2, h25, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
              · linarith only [h1, h27, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h18, h25, h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h30 | h30
          · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
            · linarith only [h2, h31, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
              · linarith only [h18, h33, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                · linarith only [h1, h35, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · linarith only [h30, h35, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
            · linarith only [h0, h2, h38, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
              · linarith only [h0, h18, h2, h40, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                · linarith only [h1, h30, h42, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h46 | h46
                      · rcases h3bigk with h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p47_1, u0elo2]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h2, hlam, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h18, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h30, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h1, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h38, hlam, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h40, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h42, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          rcases p47_3 (m.d 0 3) (by simp) with h58 | h58
                          · linarith only [h2, h58, hlam]
                          · rcases p47_3 (m.d 1 3) (by simp) with h60 | h60
                            · linarith only [h38, h60, hlam]
                            · rcases p47_3 (m.d 2 3) (by simp) with h62 | h62
                              · rcases p47_3 (m.d 3 4) (by simp) with h63 | h63
                                · linarith only [h44, h63, hlam]
                                · linarith only [h18, h63, hlam]
                              · linarith only [h2, h62, hlam]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          rcases p47_3 (m.d 0 3) (by simp) with h67 | h67
                          · linarith only [h2, h67, hlam]
                          · linarith only [h1, h67, hlam]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h2, h30, h46, hc02, hc23, hlam, hphi, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h0, h2, h30, hc12, hc23, hlam, hphi, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h0, h2, h44, hc12, hc23, hlam, hphi, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h38, h44, hc12, hc23, hlam, hphi, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h44, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h0, h2, h30, h44, hc12, hc23, hlam, hphi, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h0, h2, h45, hc12, hc23, hlam, hphi, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h38, h45, hc12, hc23, hlam, hphi, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h45, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h46, hlam, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [hlam, p47_0]
                      · rcases h3bigk with h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [hlam, p83_0]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h38, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p83_1, u0elo2]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h2, hlam, p83_1]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h18, hlam, p83_0]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h30, hlam, p83_0]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h1, hlam, p83_0]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [hlam, p83_0]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h38, hlam, p83_1]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h40, hlam, p83_0]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h42, hlam, p83_0]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          rcases p83_3 (m.d 0 3) (by simp) with h94 | h94
                          · linarith only [h2, h94, hlam]
                          · rcases p83_3 (m.d 1 3) (by simp) with h96 | h96
                            · linarith only [h38, h96, hlam]
                            · rcases p83_3 (m.d 2 3) (by simp) with h98 | h98
                              · rcases p83_3 (m.d 3 4) (by simp) with h99 | h99
                                · linarith only [h44, h99, hlam]
                                · linarith only [h18, h99, hlam]
                              · linarith only [h2, h98, hlam]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          rcases p83_3 (m.d 0 3) (by simp) with h103 | h103
                          · linarith only [h103, h2, hlam]
                          · linarith only [h1, h103, hlam]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [hlam, p83_0]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h1, h18, h38, hc12, hc23, hlam, hphi, p83_1]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h1, h30, h38, hc12, hc23, hlam, hphi, p83_1]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h1, h38, h44, hc12, hc23, hlam, hphi, p83_1]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h38, h44, hc12, hc23, hlam, hphi, p83_1]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h44, hlam, p83_0]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [hlam, p83_0]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h46, hlam, p83_0]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h1, h38, h45, hc12, hc23, hlam, hphi, p83_1]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h38, h45, hc12, hc23, hlam, hphi, p83_1]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h45, hlam, p83_0]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [h1, h18, h38, h45, hc12, hc23, hlam, hphi, p83_1]
                        · have p83_0 := h83c.1
                          have p83_1 := h83c.2.1
                          have p83_2 := h83c.2.2.1
                          have p83_3 := h83c.2.2.2
                          linarith only [hlam, p83_0]
                    · linarith only [h1, h18, h38, h44, h45, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                    · linarith only [h1, h120, h30, h38, h44, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                      · rcases h3bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [hlam, p123_0]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h38, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p123_1, u0elo2]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h2, hlam, p123_1]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h18, hlam, p123_0]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h30, hlam, p123_0]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h1, hlam, p123_0]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [hlam, p123_0]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h38, hlam, p123_1]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h40, hlam, p123_0]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h42, hlam, p123_0]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h120, h122, hc03, hc34, hlam, hphi, p123_1]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h120, h122, h38, hc12, hc34, hlam, hphi, ht23, p123_1]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [hlam, p123_0]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h44, hlam, p123_0]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h120, hlam, p123_0]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          rcases p123_3 (m.d 0 3) (by simp) with h139 | h139
                          · linarith only [h139, hlam, p123_0]
                          · rcases p123_3 (m.d 1 3) (by simp) with h141 | h141
                            · linarith only [h141, h40, hlam]
                            · rcases p123_3 (m.d 2 3) (by simp) with h143 | h143
                              · linarith only [h143, h44, hlam]
                              · linarith only [h143, h2, hlam]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          rcases p123_3 (m.d 0 3) (by simp) with h146 | h146
                          · linarith only [h146, h18, hlam]
                          · linarith only [h1, h146, hlam]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h0, h2, hc12, hc34, hlam, hphi, ht23, p123_1]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [hlam, p123_0]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h1, h30, h38, hc12, hc34, hlam, hphi, ht23, p123_1]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          rcases p123_3 (m.d 0 3) (by simp) with h152 | h152
                          · linarith only [h152, hlam, p123_0]
                          · rcases p123_3 (m.d 1 3) (by simp) with h154 | h154
                            · linarith only [h154, h42, hlam]
                            · rcases p123_3 (m.d 2 3) (by simp) with h156 | h156
                              · linarith only [h120, h156, hlam]
                              · linarith only [h156, h2, hlam]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          rcases p123_3 (m.d 0 3) (by simp) with h159 | h159
                          · linarith only [h159, h30, hlam]
                          · linarith only [h1, h159, hlam]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h0, h2, hc12, hc35, hlam, hphi, ht23, p123_1]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [h122, hlam, p123_1]
                        · have p123_0 := h123c.1
                          have p123_1 := h123c.2.1
                          have p123_2 := h123c.2.2.1
                          have p123_3 := h123c.2.2.2
                          linarith only [hlam, p123_0]
                      · linarith only [h0, h122, h2, h44, hc12, hc45, hlam, hphi, ht23, ht34]
    · linarith only [h1, hc01, hlam, hphi, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA3_H_L_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
  · linarith only [h0, hc01, hlam, hphi, u1elo3]

theorem n7l_sAA3_H_L_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi0]

theorem n7l_sAA3_H_L_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi0]

theorem n7l_sAA3_H_L_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi0]

theorem n7l_sAA3_H_L_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1ehi := hb1.2.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]
    · linarith only [h2, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]

theorem n7l_sAA3_H_L_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_H_L_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
      · linarith only [h0, h2, h4, hc12, hlam, hphi, u1ehi0]
      · linarith only [h0, h4, hc23, hlam, hphi, ht12, u1ehi0]

theorem n7l_sAA3_H_L_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · linarith only [h20, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h20, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h27 | h27
    · linarith only [h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h27, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h30 | h30
    · linarith only [h30, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h30, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h34, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h38 | h38
    · linarith only [h38, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h38, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h41 | h41
    · linarith only [h41, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h41, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h44 | h44
    · linarith only [h44, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h44, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_H_L_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hlam, hphi, p0_1, u1elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hlam, hphi, p0_1, u1elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hlam, hphi, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hlam, hphi, p0_1, u1elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_H_L_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
        · linarith only [h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
          · linarith only [h0, h1, h3, h5, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
            · linarith only [h5, h9, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · linarith only [h0, h1, h9, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
    · linarith only [h12, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h14 | h14
      · linarith only [h14, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h16 | h16
        · linarith only [h16, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
          · linarith only [h0, h14, h18, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
            · linarith only [h16, h20, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
              · linarith only [h12, h20, h22, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h18, h22, hc01, hc34, hlam, hphi, ht12, ht23]

theorem n7l_sAA3_H_L_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi7 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi7]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo2]

theorem n7l_sAA3_H_L_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi6]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA3_H_L_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi6]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA3_H_R_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAA3_H_R_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA3_H_R_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA3_H_R_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA3_H_R_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAA3_H_R_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h10, h12, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
                          · rcases h3bigk with h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h0, h2, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p14_1, u1ehi4]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              rcases p14_3 (m.d 0 3) (by simp) with h17 | h17
                              · rcases p14_3 (m.d 1 3) (by simp) with h18 | h18
                                · linarith only [h1, h18, hlam]
                                · linarith only [h18, h6, hlam]
                              · linarith only [h17, h2, hlam]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              rcases p14_3 (m.d 0 3) (by simp) with h22 | h22
                              · rcases p14_3 (m.d 1 3) (by simp) with h23 | h23
                                · linarith only [h1, h23, hlam]
                                · linarith only [h23, h7, hlam]
                              · linarith only [h22, hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              rcases p14_3 (m.d 0 3) (by simp) with h27 | h27
                              · rcases p14_3 (m.d 1 3) (by simp) with h28 | h28
                                · linarith only [h1, h28, hlam]
                                · linarith only [h28, h8, hlam]
                              · linarith only [h27, hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h1, hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h0, h11, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p14_1]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              rcases p14_3 (m.d 0 3) (by simp) with h35 | h35
                              · rcases p14_3 (m.d 1 3) (by simp) with h36 | h36
                                · rcases p14_3 (m.d 2 3) (by simp) with h37 | h37
                                  · linarith only [h37, h6, hlam]
                                  · linarith only [h10, h37, hlam]
                                · linarith only [h36, hlam, p14_0]
                              · linarith only [h3, h35, hlam]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              rcases p14_3 (m.d 0 3) (by simp) with h42 | h42
                              · rcases p14_3 (m.d 1 3) (by simp) with h43 | h43
                                · rcases p14_3 (m.d 2 3) (by simp) with h44 | h44
                                  · linarith only [h44, h6, hlam]
                                  · linarith only [h11, h44, hlam]
                                · linarith only [h43, hlam, p14_0]
                              · linarith only [h4, h42, hlam]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h2, hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h6, hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h0, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h0, h12, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h3, hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h7, hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h10, hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h12, hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h4, hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h8, hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h11, hlam, p14_0]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [h1, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                            · have p14_0 := h14c.1
                              have p14_1 := h14c.2.1
                              have p14_2 := h14c.2.2.1
                              have p14_3 := h14c.2.2.2
                              linarith only [hlam, p14_0]
                        · linarith only [h0, h10, h11, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                        · linarith only [h0, h10, h6, h65, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                          · rcases h3bigk with h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h65, h67, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              rcases p68_3 (m.d 0 3) (by simp) with h71 | h71
                              · rcases p68_3 (m.d 1 3) (by simp) with h72 | h72
                                · linarith only [h1, h72, hlam]
                                · linarith only [h6, h72, hlam]
                              · linarith only [h2, h71, hlam]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              rcases p68_3 (m.d 0 3) (by simp) with h76 | h76
                              · rcases p68_3 (m.d 1 3) (by simp) with h77 | h77
                                · linarith only [h1, h77, hlam]
                                · linarith only [h7, h77, hlam]
                              · linarith only [h76, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              rcases p68_3 (m.d 0 3) (by simp) with h81 | h81
                              · rcases p68_3 (m.d 1 3) (by simp) with h82 | h82
                                · linarith only [h1, h82, hlam]
                                · linarith only [h8, h82, hlam]
                              · linarith only [h81, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h1, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              rcases p68_3 (m.d 0 3) (by simp) with h88 | h88
                              · rcases p68_3 (m.d 1 3) (by simp) with h89 | h89
                                · rcases p68_3 (m.d 2 3) (by simp) with h90 | h90
                                  · linarith only [h6, h90, hlam]
                                  · rcases p68_3 (m.d 3 4) (by simp) with h92 | h92
                                    · linarith only [h7, h92, hlam]
                                    · linarith only [h10, h92, hlam]
                                · linarith only [h6, h89, hlam]
                              · linarith only [h2, h88, hlam]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h1, h65, h67, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h0, h6, h65, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h2, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h6, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h10, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h65, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h3, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h7, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h0, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h0, h6, h65, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h4, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h8, hlam, p68_0]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h0, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [h67, hlam, p68_1]
                            · have p68_0 := h68c.1
                              have p68_1 := h68c.2.1
                              have p68_2 := h68c.2.2.1
                              have p68_3 := h68c.2.2.2
                              linarith only [hlam, p68_0]
                          · linarith only [h0, h10, h6, h67, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
                  · linarith only [h8, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                · linarith only [h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
              · linarith only [h6, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
          · linarith only [h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA3_H_R_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h1, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
        · linarith only [h0, h1, h2, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
      · linarith only [h2, hc35, hlam, hphi, ht12, ht23, u1ehi2]
    · linarith only [h1, hc23, hlam, hphi, ht12, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA3_H_R_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAA3_H_R_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h3ehi := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · linarith only [h5, hc13, hlam, hphi, p0_1, u1ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h7 | h7
          · linarith only [h7, hc14, hlam, hphi, p0_1, u1ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h9 | h9
            · linarith only [h9, hc15, hlam, hphi, p0_1, u1ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
                · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h15 | h15
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
                        · linarith only [h16, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                        · linarith only [h16, h5, hlam]
                      · linarith only [h15, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h14, h9, hlam, p0_1]
                  · linarith only [h13, h7, hlam, p0_1]
                · linarith only [h12, hc13, hlam, hphi, ht01, u0ehi0]
              · linarith only [h11, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · rcases p0_3 (m.d 1 2) (by simp) with h26 | h26
      · linarith only [h26, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h28 | h28
        · linarith only [h28, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h30 | h30
          · linarith only [h30, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h32 | h32
            · linarith only [h32, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h34 | h34
              · rcases m.htr 0 1 3 (by decide) (by decide) with h35 | h35
                · rcases m.htr 0 1 4 (by decide) (by decide) with h36 | h36
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h37 | h37
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h38 | h38
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                        · linarith only [h26, h39, hlam]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                              · linarith only [h43, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                              · linarith only [h30, h43, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h46 | h46
                              · linarith only [h46, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                              · linarith only [h30, h46, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h50 | h50
                              · linarith only [h50, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                              · linarith only [h30, h50, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
                              · linarith only [h53, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                              · linarith only [h30, h53, hlam]
                      · linarith only [h38, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h37, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                  · linarith only [h36, hc14, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h35, hlam, p0_0]
              · linarith only [h34, hc12, hlam, hphi, p0_1, u1ehi2]
    · linarith only [h25, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h62 | h62
    · rcases p0_3 (m.d 1 2) (by simp) with h63 | h63
      · linarith only [h63, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h65 | h65
        · linarith only [h65, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h67 | h67
          · linarith only [h67, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h69 | h69
            · linarith only [h69, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
              · rcases m.htr 0 1 3 (by decide) (by decide) with h72 | h72
                · rcases m.htr 0 1 4 (by decide) (by decide) with h73 | h73
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h74 | h74
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h75 | h75
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                        · linarith only [h63, h76, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                          · linarith only [h63, h78, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                              · linarith only [h65, h81, hlam]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
                                · linarith only [h81, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi4]
                                · linarith only [h76, h80, h83, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                              · linarith only [h65, h86, hlam]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                                · linarith only [h86, h88, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi4]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                                    · linarith only [h71, h75, h86, h91, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                    · linarith only [h76, h91, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                  · linarith only [h69, h90, hlam]
                      · linarith only [h75, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h74, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h73, hlam, p0_0]
                · linarith only [h63, h72, hc13, hlam, hphi, p0_1, u1ehi1]
              · linarith only [h63, h71, hlam, p0_1]
    · linarith only [h62, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h101 | h101
    · rcases p0_3 (m.d 1 2) (by simp) with h102 | h102
      · linarith only [h102, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h104 | h104
        · linarith only [h104, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h106 | h106
          · linarith only [h106, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h108 | h108
            · linarith only [h108, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h110 | h110
              · rcases m.htr 0 1 3 (by decide) (by decide) with h111 | h111
                · rcases m.htr 0 1 4 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h113 | h113
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h114 | h114
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
                        · linarith only [h102, h115, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
                            · linarith only [h102, h118, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h120 | h120
                              · linarith only [h104, h120, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                              · linarith only [h115, h117, h120, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h123 | h123
                            · linarith only [h102, h123, hlam]
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h125 | h125
                              · linarith only [h104, h125, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                              · rcases m.htr 1 3 5 (by decide) (by decide) with h127 | h127
                                · linarith only [h104, h127, hlam]
                                · rcases m.htr 1 4 5 (by decide) (by decide) with h129 | h129
                                  · linarith only [h106, h129, hlam]
                                  · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
                                    · linarith only [h110, h114, h115, h125, h131, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                    · linarith only [h115, h131, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                      · linarith only [h114, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h113, hlam, p0_0]
                  · linarith only [h106, h112, hlam, p0_1]
                · linarith only [h111, hc13, hlam, hphi, ht01, u0ehi0]
              · linarith only [h110, hc12, hlam, hphi, p0_1, u1ehi4]
    · linarith only [h101, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_H_R_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA3_H_R_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA3_H_R_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA3_H_R_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA3_H_R_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA3_H_R_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA3_M_IR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
    linarith only [hc02, hlam, hphi, ht23, p0_1, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3, u3elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4, u3elo0]
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

theorem n7l_sAA3_M_IR_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAA3_M_IR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAA3_M_IR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA3_M_IR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA3_M_IR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA3_M_IR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAA3_M_IR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1ehi := hb1.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
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
    linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
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
    linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
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
    linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
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
    linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
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

theorem n7l_sAA3_M_IR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h2, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h0, h2, h3, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · linarith only [h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
        · linarith only [h3, hc34, hlam, hphi, ht12, ht23, u1ehi2]
      · linarith only [h2, hc23, hlam, hphi, ht12, u1ehi1]
    · linarith only [h1, hc13, hlam, hphi, u1ehi0]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA3_M_IR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h3elo := hb3.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h11, h13, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h11, h12, h13, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                            · linarith only [h1, h12, h16, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · rcases h1bigk with h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h10, h11, h12, h5, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h10, h11, h12, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h10, h11, h12, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                rcases p18_3 (m.d 0 1) (by simp) with h23 | h23
                                · rcases p18_3 (m.d 1 2) (by simp) with h24 | h24
                                  · linarith only [h0, h24, hlam]
                                  · linarith only [h24, h7, hlam]
                                · linarith only [h23, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h0, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h10, h11, h12, h8, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18_1]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h0, h10, h11, h12, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p18_1, u1ehi4]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h1, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h5, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h10, h11, h12, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p18_1]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h1, hlam, hphi, ht12, ht23, p18_1, u1ehi4, u3elo0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h2, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h6, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h8, hlam, p18_1]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h1, h8, hlam, hphi, ht12, ht23, p18_1, u1ehi4, u3elo0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h3, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h7, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h9, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h10, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [hlam, p18_0]
                        · linarith only [h1, h11, h8, hc23, hlam, hphi, u3elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                          · linarith only [h10, h50, hc24, hlam, hphi, ht12, u1ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                            · linarith only [h10, h52, hlam, hphi, ht12, ht23, u1ehi3, u3elo3]
                            · rcases h1bigk with h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h49, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p54_1]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                rcases p54_3 (m.d 0 1) (by simp) with h57 | h57
                                · rcases p54_3 (m.d 1 2) (by simp) with h58 | h58
                                  · linarith only [h0, h58, hlam]
                                  · linarith only [h5, h58, hlam]
                                · linarith only [h57, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                rcases p54_3 (m.d 0 1) (by simp) with h62 | h62
                                · rcases p54_3 (m.d 1 2) (by simp) with h63 | h63
                                  · linarith only [h0, h63, hlam]
                                  · linarith only [h6, h63, hlam]
                                · linarith only [h62, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                rcases p54_3 (m.d 0 1) (by simp) with h67 | h67
                                · rcases p54_3 (m.d 1 2) (by simp) with h68 | h68
                                  · linarith only [h0, h68, hlam]
                                  · linarith only [h68, h7, hlam]
                                · linarith only [h67, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h0, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h10, h9, hc12, hlam, hphi, p54_1, u1ehi3]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p54_1, u1ehi3]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p54_1, u1ehi3]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h1, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h5, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [hc13, hlam, hphi, p54_1, u1ehi3]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h1, h10, hlam, hphi, ht12, ht23, p54_1, u1ehi3, u3elo0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h2, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h6, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h8, hlam, p54_1]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h10, hlam, p54_1]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h3, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h7, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [h9, hlam, p54_0]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [hc15, hlam, hphi, p54_1, u1ehi3]
                              · have p54_0 := h54c.1
                                have p54_1 := h54c.2.1
                                have p54_2 := h54c.2.2.1
                                have p54_3 := h54c.2.2.2
                                linarith only [hlam, p54_0]
                        · linarith only [h1, h49, h8, hc23, hlam, hphi, u3elo0]
                    · linarith only [h9, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
                  · linarith only [h8, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h96 | h96
                    · linarith only [h5, h7, h96, hlam]
                    · linarith only [h96, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
                  · linarith only [h95, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h100 | h100
                · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                  · linarith only [h101, h5, h6, hlam]
                  · linarith only [h101, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
                  · linarith only [h104, h5, h6, hlam]
                  · linarith only [h104, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
            · linarith only [h5, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
            · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
              · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
                · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h112 | h112
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                      · linarith only [h108, h111, h113, h4, hc12, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h116 | h116
                          · linarith only [h108, h115, h116, h4, hc12, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h118 | h118
                            · linarith only [h0, h108, h115, h118, h4, hc01, hlam, hphi, u0ehi3]
                            · rcases h1bigk with h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c | h120c
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h108, h115, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p120_1]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                rcases p120_3 (m.d 0 1) (by simp) with h123 | h123
                                · rcases p120_3 (m.d 1 2) (by simp) with h124 | h124
                                  · linarith only [h0, h124, hlam]
                                  · linarith only [h108, h124, hlam]
                                · linarith only [h123, hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                rcases p120_3 (m.d 0 1) (by simp) with h128 | h128
                                · rcases p120_3 (m.d 1 2) (by simp) with h129 | h129
                                  · linarith only [h0, h129, hlam]
                                  · linarith only [h109, h129, hlam]
                                · linarith only [h128, hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                rcases p120_3 (m.d 0 1) (by simp) with h133 | h133
                                · rcases p120_3 (m.d 1 2) (by simp) with h134 | h134
                                  · linarith only [h0, h134, hlam]
                                  · linarith only [h110, h134, hlam]
                                · linarith only [h133, hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h0, hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h112, h113, hc12, hlam, hphi, p120_1, u1ehi3]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p120_1, u1ehi3]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p120_1, u1ehi4]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h1, hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h108, hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [hc13, hlam, hphi, p120_1, u1ehi3]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h1, hlam, hphi, ht12, ht23, p120_1, u1ehi4, u3elo0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h2, hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h109, hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h111, hlam, p120_1]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h113, hlam, p120_1]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h3, hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h110, hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [h112, hlam, p120_0]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [hc15, hlam, hphi, p120_1, u1ehi3]
                              · have p120_0 := h120c.1
                                have p120_1 := h120c.2.1
                                have p120_2 := h120c.2.2.1
                                have p120_3 := h120c.2.2.2
                                linarith only [hlam, p120_0]
                        · linarith only [h1, h111, h115, hc23, hlam, hphi, u3elo0]
                    · linarith only [h112, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
                  · linarith only [h111, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                    · linarith only [h108, h110, h162, hlam]
                    · linarith only [h162, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
                  · linarith only [h161, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h166 | h166
                · rcases m.htr 1 3 4 (by decide) (by decide) with h167 | h167
                  · linarith only [h108, h109, h167, hlam]
                  · linarith only [h167, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h170 | h170
                  · linarith only [h108, h109, h170, hlam]
                  · linarith only [h170, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
            · linarith only [h108, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h177 | h177
    · linarith only [h0, h177, hc12, hlam, hphi, u1ehi2]
    · linarith only [h177, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem n7l_sAA3_M_IR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h3ehi := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · linarith only [h5, hc13, hlam, hphi, p0_1, u1ehi1]
        · rcases p0_3 (m.d 1 4) (by simp) with h7 | h7
          · linarith only [h7, hc14, hlam, hphi, p0_1, u1ehi1]
          · rcases p0_3 (m.d 1 5) (by simp) with h9 | h9
            · linarith only [h9, hc15, hlam, hphi, p0_1, u1ehi1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
                · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                      · linarith only [h15, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · linarith only [h15, h5, hlam]
                    · linarith only [h14, h9, hlam, p0_1]
                  · linarith only [h13, h7, hlam, p0_1]
                · linarith only [h12, hc13, hlam, hphi, p0_1, u1ehi1]
              · linarith only [h11, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · rcases p0_3 (m.d 1 2) (by simp) with h24 | h24
      · linarith only [h24, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h26 | h26
        · linarith only [h26, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h28 | h28
          · linarith only [h28, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h30 | h30
            · linarith only [h30, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h32 | h32
              · rcases m.htr 0 1 3 (by decide) (by decide) with h33 | h33
                · rcases m.htr 0 1 4 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
                      · linarith only [h24, h36, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                            · linarith only [h40, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                            · linarith only [h28, h40, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                            · linarith only [h43, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                            · linarith only [h28, h43, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                            · linarith only [h47, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                            · linarith only [h28, h47, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h50 | h50
                            · linarith only [h50, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                            · linarith only [h28, h50, hlam]
                    · linarith only [h35, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                  · linarith only [h34, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
                · linarith only [h33, hlam, p0_0]
              · linarith only [h32, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
    · linarith only [h23, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h58 | h58
    · rcases p0_3 (m.d 1 2) (by simp) with h59 | h59
      · linarith only [h59, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h61 | h61
        · linarith only [h61, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h63 | h63
          · linarith only [h63, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h65 | h65
            · linarith only [h65, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h67 | h67
              · rcases m.htr 0 1 3 (by decide) (by decide) with h68 | h68
                · rcases m.htr 0 1 4 (by decide) (by decide) with h69 | h69
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h70 | h70
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                      · linarith only [h59, h71, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                        · linarith only [h59, h73, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                            · linarith only [h61, h76, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                              · linarith only [h76, h78, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi4]
                              · linarith only [h71, h75, h78, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                            · linarith only [h61, h81, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
                              · linarith only [h81, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi4]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                                  · linarith only [h71, h81, h86, hc23, hlam, hphi, ht12, u1ehi1]
                                  · linarith only [h71, h86, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h65, h85, hlam]
                    · linarith only [h70, hc15, hlam, hphi, p0_1, u1ehi3]
                  · linarith only [h69, hlam, p0_0]
                · linarith only [h68, hc13, hlam, hphi, p0_1, u1ehi3]
              · linarith only [h59, h67, hlam, p0_1]
    · linarith only [h58, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h95 | h95
    · rcases p0_3 (m.d 1 2) (by simp) with h96 | h96
      · linarith only [h96, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h98 | h98
        · linarith only [h98, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
          · linarith only [h100, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h102 | h102
            · linarith only [h102, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h104 | h104
              · rcases m.htr 0 1 3 (by decide) (by decide) with h105 | h105
                · rcases m.htr 0 1 4 (by decide) (by decide) with h106 | h106
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
                      · linarith only [h108, h96, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                          · linarith only [h111, h96, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                            · linarith only [h113, h98, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                            · linarith only [h108, h110, h113, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                          · linarith only [h116, h96, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                            · linarith only [h118, h98, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u3ehi3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h120 | h120
                              · linarith only [h120, h98, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h122 | h122
                                · linarith only [h100, h122, hlam]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                                  · linarith only [h108, h118, h124, hc23, hlam, hphi, ht12, u1ehi1]
                                  · linarith only [h108, h124, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h107, hlam, p0_0]
                  · linarith only [h106, hc14, hlam, hphi, p0_1, u1ehi4]
                · linarith only [h100, h105, hc13, hlam, hphi, p0_1, u1ehi3]
              · linarith only [h100, h104, hc12, hlam, hphi, p0_1, u1ehi3]
    · linarith only [h95, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_M_IR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc23 := m.hcor 2 3 (by decide)
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
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · rcases h0emin with h5 | h5 | h5 | h5 | h5
            · linarith only [h5, hlam, ht01, u1elo0]
            · linarith only [h0, h5, hlam, ht01, u1elo0]
            · linarith only [h5, hlam, ht01, ht12, ht23, u3elo0]
            · linarith only [h1, h5, hlam, ht01, ht12, ht23, u3elo0]
            · linarith only [h2, h5, hlam, ht01, ht12, ht23, u3elo0]
          · linarith only [h2, h4, hc23, hlam, hphi, u3elo0]
        · linarith only [h1, h3, hc23, hlam, hphi, u3elo0]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem n7l_sAA3_M_IR_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAA3_M_IR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
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
        · linarith only [h1, h3, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi1]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
    · linarith only [h1, hlam, hphi, ht01, u0ehi0, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo1]

theorem n7l_sAA3_M_IR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA3_M_IR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAA3_M_IR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA3_M_LI_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h26 | h26
    · linarith only [h26, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h26, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h30 | h30
    · linarith only [h30, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h30, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h34, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_M_LI_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_M_LI_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h9 | h9
    · linarith only [h9, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h9, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h12 | h12
    · linarith only [h12, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h12, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h16 | h16
    · linarith only [h16, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h16, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · linarith only [h20, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h20, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h27 | h27
    · linarith only [h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h27, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_M_LI_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3elo := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
          · linarith only [h2, h4, h6, hc12, hlam, hphi, ht23, u3elo2]
          · linarith only [h2, h6, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h1, hc01, hlam, hphi, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA3_M_LI_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
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
        · linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA3_M_LI_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
  · linarith only [h0, hc01, hlam, hphi, u1elo2]

theorem n7l_sAA3_M_LI_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAA3_M_LI_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
  · linarith only [h0, hc13, hlam, hphi, u1ehi0]

theorem n7l_sAA3_M_LI_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
  · linarith only [h0, hc13, hlam, hphi, u1ehi0]

theorem n7l_sAA3_M_LI_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h3, h5, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h0, h3, h4, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h4, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
        · linarith only [h3, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
    · linarith only [h0, h12, hc12, hlam, hphi, u1ehi2]
    · linarith only [h12, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem n7l_sAA3_M_LI_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h0, h3, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h12 | h12
                · linarith only [h12, h6, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                  · linarith only [h0, h14, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h0, h14, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h17 | h17
              · rcases m.htr 0 3 5 (by decide) (by decide) with h18 | h18
                · linarith only [h18, h3, h5, hlam]
                · linarith only [h17, h18, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
                · linarith only [h17, h21, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                  · linarith only [h0, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h23, h3, h5, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h26 | h26
            · rcases m.htr 0 3 4 (by decide) (by decide) with h27 | h27
              · linarith only [h27, h3, h4, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h29 | h29
                · linarith only [h27, h29, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                  · linarith only [h0, h31, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h3, h31, h4, hc12, hc24, hlam, hphi]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h34 | h34
              · linarith only [h3, h34, h4, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h36 | h36
                · linarith only [h34, h36, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
                  · linarith only [h0, h38, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h3, h38, h4, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h41 | h41
          · rcases m.htr 0 2 5 (by decide) (by decide) with h42 | h42
            · rcases m.htr 0 3 4 (by decide) (by decide) with h43 | h43
              · rcases m.htr 0 3 5 (by decide) (by decide) with h44 | h44
                · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
                  · linarith only [h0, h3, h45, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
                        · linarith only [h1, h49, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h43, h45, h47, h49, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi3]
                      · linarith only [h42, h47, h48, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi3]
                    · linarith only [h3, h41, h47, hc12, hc23, hlam, hphi]
                · linarith only [h43, h44, hc35, hlam, hphi, u3ehi3]
              · linarith only [h3, h41, h43, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h56 | h56
              · rcases m.htr 0 3 5 (by decide) (by decide) with h57 | h57
                · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                  · linarith only [h0, h58, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
                      · linarith only [h0, h42, h61, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
                        · linarith only [h1, h63, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h56, h63, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · linarith only [h41, h60, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                · linarith only [h56, h57, hc35, hlam, hphi, u3ehi3]
              · linarith only [h3, h41, h56, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h69 | h69
            · rcases m.htr 0 3 4 (by decide) (by decide) with h70 | h70
              · rcases m.htr 0 3 5 (by decide) (by decide) with h71 | h71
                · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                  · linarith only [h0, h3, h72, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                    · linarith only [h2, h41, h69, h74, hc12, hlam, hphi, u1ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                        · linarith only [h1, h77, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h70, h77, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h41, h69, h76, hc12, hc24, hlam, hphi]
                · linarith only [h70, h71, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h82 | h82
                · linarith only [h70, h82, hc34, hlam, hphi, u3ehi4]
                · linarith only [h3, h69, h82, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h85 | h85
              · rcases m.htr 0 3 5 (by decide) (by decide) with h86 | h86
                · rcases m.htr 1 2 3 (by decide) (by decide) with h87 | h87
                  · linarith only [h0, h3, h87, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                    · linarith only [h0, h41, h89, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h91 | h91
                      · linarith only [h0, h69, h91, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
                        · linarith only [h1, h93, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h85, h93, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                · linarith only [h85, h86, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h97 | h97
                · linarith only [h85, h97, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
                  · linarith only [h0, h3, h99, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
                    · linarith only [h0, h101, h41, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
                      · linarith only [h0, h103, h2, h3, h69, hc23, hlam, hphi, ht12, u1ehi4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h105 | h105
                        · linarith only [h1, h105, h3, h85, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
                          · linarith only [h1, h107, h97, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                            · linarith only [h1, h109, h85, h99, hc23, hlam, hphi, ht12, u1ehi1]
                            · linarith only [h0, h109, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h114 | h114
    · linarith only [h0, h114, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h116 | h116
      · linarith only [h0, h116, hc12, hlam, hphi, u1ehi4]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h118 | h118
        · rcases m.htr 0 2 4 (by decide) (by decide) with h119 | h119
          · rcases m.htr 0 2 5 (by decide) (by decide) with h120 | h120
            · rcases m.htr 0 3 4 (by decide) (by decide) with h121 | h121
              · rcases m.htr 0 3 5 (by decide) (by decide) with h122 | h122
                · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h127 | h127
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                            · linarith only [h118, h128, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · linarith only [h118, h121, h128, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                          · linarith only [h118, h122, h127, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                        · linarith only [h114, h121, h126, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi0]
                      · linarith only [h0, h120, h125, hlam]
                    · linarith only [h0, h119, h124, hlam]
                  · linarith only [h0, h123, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h121, h122, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h137 | h137
                · linarith only [h121, h137, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h139 | h139
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h140 | h140
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h141 | h141
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h142 | h142
                        · linarith only [h114, h121, h139, h142, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h114, h142, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h120, h141, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                    · linarith only [h0, h119, h140, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi0]
                  · linarith only [h0, h118, h139, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h148 | h148
              · rcases m.htr 0 3 5 (by decide) (by decide) with h149 | h149
                · linarith only [h118, h120, h149, hlam]
                · linarith only [h148, h149, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h152 | h152
                · linarith only [h148, h152, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h155 | h155
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
                      · linarith only [h118, h120, h156, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h156, hc25, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h114, h119, h154, h155, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                  · linarith only [h0, h154, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h161 | h161
            · rcases m.htr 0 3 4 (by decide) (by decide) with h162 | h162
              · linarith only [h118, h119, h162, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h164 | h164
                · linarith only [h162, h164, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
                    · linarith only [h118, h119, h167, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h167, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h118, h166, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h171 | h171
              · linarith only [h118, h119, h171, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h173 | h173
                · linarith only [h171, h173, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h176 | h176
                    · linarith only [h118, h119, h176, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h176, hc24, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h118, h175, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h180 | h180
          · rcases m.htr 0 2 5 (by decide) (by decide) with h181 | h181
            · rcases m.htr 0 3 4 (by decide) (by decide) with h182 | h182
              · rcases m.htr 0 3 5 (by decide) (by decide) with h183 | h183
                · rcases m.htr 1 2 3 (by decide) (by decide) with h184 | h184
                  · linarith only [h0, h118, h184, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h184, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h182, h183, hc35, hlam, hphi, u3ehi3]
              · linarith only [h118, h180, h182, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h189 | h189
              · rcases m.htr 0 3 5 (by decide) (by decide) with h190 | h190
                · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
                  · linarith only [h0, h118, h191, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h191, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h189, h190, hc35, hlam, hphi, u3ehi3]
              · linarith only [h118, h180, h189, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h196 | h196
            · rcases m.htr 0 3 4 (by decide) (by decide) with h197 | h197
              · rcases m.htr 0 3 5 (by decide) (by decide) with h198 | h198
                · rcases m.htr 1 2 3 (by decide) (by decide) with h199 | h199
                  · linarith only [h116, h118, h196, h199, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h199, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h197, h198, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h203 | h203
                · linarith only [h197, h203, hc34, hlam, hphi, u3ehi4]
                · linarith only [h118, h196, h203, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h206 | h206
              · rcases m.htr 0 3 5 (by decide) (by decide) with h207 | h207
                · rcases m.htr 1 2 3 (by decide) (by decide) with h208 | h208
                  · linarith only [h0, h118, h208, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h208, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h206, h207, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h212 | h212
                · linarith only [h206, h212, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h214 | h214
                  · linarith only [h0, h118, h214, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h0, h214, hc23, hlam, hphi, ht12, u1ehi0]

theorem n7l_sAA3_M_LI_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAA3_M_LI_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi9 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi9, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo4]

theorem n7l_sAA3_M_LI_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA3_M_LR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht23, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u3elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h26 | h26
    · linarith only [h26, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h26, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h30 | h30
    · linarith only [h30, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h30, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h34, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_M_LR_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1bigk := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_M_LR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h9 | h9
    · linarith only [h9, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h9, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h12 | h12
    · linarith only [h12, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h12, hc01, hc12, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h16 | h16
    · linarith only [h16, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h16, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · linarith only [h20, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h20, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hc13, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h27 | h27
    · linarith only [h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h27, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1, u3ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_M_LR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi5, u1elo0]

theorem n7l_sAA3_M_LR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi5, u1elo0]

theorem n7l_sAA3_M_LR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi5, u1elo0]

theorem n7l_sAA3_M_LR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAA3_M_LR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA3_M_LR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA3_M_LR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
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
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h3, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
            · linarith only [h0, h3, h4, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h4, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
        · linarith only [h3, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
    · linarith only [h0, h12, hc12, hlam, hphi, u1ehi2]
    · linarith only [h12, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem n7l_sAA3_M_LR_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAA3_M_LR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
            · linarith only [h1, h6, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
            · linarith only [h1, h3, h6, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
          · linarith only [h0, h9, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
            · linarith only [h1, h11, h3, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
              · linarith only [h11, h13, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                  · linarith only [h16, h3, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                    · rcases h1bigk with h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [hlam, p19_0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        rcases p19_3 (m.d 0 1) (by simp) with h21 | h21
                        · rcases p19_3 (m.d 1 2) (by simp) with h22 | h22
                          · linarith only [h22, hlam, p19_0]
                          · rcases p19_3 (m.d 1 3) (by simp) with h24 | h24
                            · linarith only [h1, h24, hlam]
                            · linarith only [h24, h9, hlam]
                        · linarith only [h21, hlam, p19_0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19_1, u1elo0, u3ehi1]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h15, hc45, hlam, hphi, ht01, ht0b, ht5b, p19_1, u1elo0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19_1, u1elo0, u3ehi1]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h0, hlam, p19_0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [hlam, p19_0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h9, hlam, p19_1]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h13, h15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19_1, u1elo1, u3ehi1]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19_1, u1elo1, u3ehi1]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h1, hlam, p19_0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h13, hc12, hc35, hlam, hphi, ht23, p19_1]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [hlam, p19_0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h11, hlam, p19_0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h13, hlam, p19_1]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h2, hlam, p19_0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p19_1, u1elo0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19_1, u1elo0, u3ehi1]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [hlam, p19_0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p19_1, u1elo0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [hc01, hlam, hphi, p19_1, u1elo4]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h15, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p19_1, u0elo0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h15, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1, u0elo0, u3ehi1]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [h15, hlam, p19_0]
                      · have p19_0 := h19c.1
                        have p19_1 := h19c.2.1
                        have p19_2 := h19c.2.2.1
                        have p19_3 := h19c.2.2.2
                        linarith only [hlam, p19_0]
                    · linarith only [h16, h18, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                  · linarith only [h3, h52, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                    · linarith only [h11, h15, h54, hc34, hlam, hphi, u3ehi1]
                    · linarith only [h52, h54, hc45, hlam, hphi, ht34, u3ehi2]
      · linarith only [h2, hlam, hphi, ht01, u0ehi5, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi6, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem n7l_sAA3_M_LR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA3_M_LR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

theorem n7l_sAA3_M_LR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi6 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi6, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo1]

end R2N4
