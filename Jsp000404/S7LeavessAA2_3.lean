import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAA2_H_I_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h2elo := hb2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases h0emin with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, ht01, ht12, u2elo0]
        · linarith only [h0, h3, hlam, ht01, u1elo0]
        · linarith only [h1, h3, hlam, ht01, u1elo0]
        · linarith only [h2, h3, hlam, ht01, u1elo0]
      · linarith only [h0, h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
  · linarith only [h0, hc01, hlam, hphi, u1elo2]

theorem n7l_sAA2_H_I_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_H_I_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
  · linarith only [h0, hc01, hlam, hphi, u1elo2]

theorem n7l_sAA2_H_I_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  linarith only [hlam, hphi, ht12, u1ehi1, u2elo1]

theorem n7l_sAA2_H_I_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emax := hb0.2.2
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
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases h0emax with h5 | h5 | h5 | h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · linarith only [h0, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · linarith only [h1, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
            · linarith only [h2, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
            · linarith only [h3, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
          · linarith only [h2, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA2_H_I_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h3, h7, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h3, h7, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h3, h5, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
            · linarith only [h5, hc34, hlam, hphi, ht12, ht23, u1ehi2]
          · linarith only [h4, hc24, hlam, hphi, ht12, u1ehi1]
        · linarith only [h3, hc23, hlam, hphi, ht12, u1ehi1]
      · linarith only [h1, h2, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
    · linarith only [h1, hc14, hlam, hphi, u1ehi0]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA2_H_I_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.2.1
  have h2elo := hb2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases h0bigk with h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [hlam, p14_0]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h0, h13, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h1, h11, h12, hc01, hc45, hlam, hphi, ht0b, ht5b, p14_1]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h12, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p14_1, u1ehi4]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p14_1, u1ehi4]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h0, hlam, p14_0]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [hlam, p14_0]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h12, h2, h6, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p14_1, u1ehi4]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h12, h2, hlam, hphi, ht12, p14_1, u1ehi4, u2elo0]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h3, hlam, hphi, ht12, p14_1, u1ehi4, u2elo0]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h1, hlam, p14_0]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h0, h13, h8, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [hlam, p14_0]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h1, h12, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p14_1, u1ehi4]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h1, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p14_1, u1ehi4]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h2, hlam, p14_0]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h4, hlam, p14_0]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h6, hlam, p14_0]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [hlam, p14_0]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p14_1, u1ehi4]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h3, hlam, p14_0]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h5, hlam, p14_1]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h1, h11, h12, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p14_1, u1ehi4]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [h7, hlam, p14_1]
                              · obtain ⟨p14_0, p14_1, p14_2, p14_3⟩ := h14c
                                linarith only [hlam, p14_0]
                            · rcases h0bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [hlam, p40_0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h0, h11, h13, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p40_1]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h1, h11, h13, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p40_1]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h0, h11, h12, h13, h2, h8, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p40_1, u1ehi4, u2elo0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h0, h11, h13, h3, h8, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p40_1, u1ehi4, u2elo0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h0, hlam, p40_0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [hlam, p40_0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h1, h11, h13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p40_1, u2elo0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h12, h2, hlam, hphi, ht12, p40_1, u1ehi4, u2elo0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h3, hlam, hphi, ht12, p40_1, u1ehi4, u2elo0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h1, hlam, p40_0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h0, h10, hc03, hc25, hlam, hphi, ht0b, ht5b, p40_1]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [hlam, p40_0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h1, h12, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p40_1, u1ehi4]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h0, h1, h11, h13, h3, h8, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p40_1, u1ehi4, u2elo0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h2, hlam, p40_0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h4, hlam, p40_0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h6, hlam, p40_0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [hlam, p40_0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h0, h11, h13, h3, h8, hc04, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p40_1, u1ehi4, u2elo0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h3, hlam, p40_0]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h5, hlam, p40_1]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h1, h11, h13, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p40_1]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [h7, hlam, p40_1]
                              · obtain ⟨p40_0, p40_1, p40_2, p40_3⟩ := h40c
                                linarith only [hlam, p40_0]
                          · linarith only [h12, h4, h7, hlam, hphi, ht12, u1ehi3, u2elo0]
                        · linarith only [h11, h4, h6, hlam, hphi, ht12, u1ehi2, u2elo0]
                      · linarith only [h10, h8, hlam, hphi, ht12, u1ehi2, u2elo4]
                    · linarith only [h8, h9, hlam, hphi, ht12, u1ehi2, u2elo3]
                  · linarith only [h8, hlam, hphi, ht12, u1ehi1, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h73 | h73
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h74 | h74
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                          · linarith only [h2, h7, h75, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                            · rcases h0bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [hlam, p78_0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h0, h71, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p78_1]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi2]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi3]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h2, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi3]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h0, hlam, p78_0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [hlam, p78_0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h1, h74, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi3]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h2, hlam, hphi, ht12, p78_1, u1ehi3, u2elo0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h2, h7, hlam, hphi, ht12, p78_1, u1ehi3, u2elo0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h1, hlam, p78_0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h0, h71, h77, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p78_1]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [hlam, p78_0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h1, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi3]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h1, h2, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi3]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h2, hlam, p78_0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h4, hlam, p78_0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h6, hlam, p78_0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [hlam, p78_0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h7, hlam, p78_0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h3, hlam, p78_0]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h5, hlam, p78_1]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h1, h74, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi3]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [h2, h5, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi3]
                              · obtain ⟨p78_0, p78_1, p78_2, p78_3⟩ := h78c
                                linarith only [hlam, p78_0]
                            · rcases h0bigk with h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [hlam, p104_0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h0, h71, h74, h77, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p104_1]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h1, h74, h77, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p104_1]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h0, h2, h71, h74, h77, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p104_1, u1ehi3, u2elo0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h0, h3, h71, h74, h75, h77, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p104_1, u1ehi3, u2elo0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h0, hlam, p104_0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [hlam, p104_0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h1, h74, h77, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p104_1, u2elo0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h2, hlam, hphi, ht12, p104_1, u1ehi3, u2elo0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h3, h75, hlam, hphi, ht12, p104_1, u1ehi3, u2elo0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h1, hlam, p104_0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h0, h73, hc03, hc25, hlam, hphi, ht0b, ht5b, p104_1]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [hlam, p104_0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h1, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p104_1, u1ehi3]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h0, h1, h3, h71, h74, h75, h77, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p104_1, u1ehi3, u2elo0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h2, hlam, p104_0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h4, hlam, p104_0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h6, hlam, p104_0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [hlam, p104_0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h7, hlam, p104_0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h3, hlam, p104_0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h5, hlam, p104_1]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h1, h74, h77, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p104_1]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [h2, h5, hlam, hphi, ht12, p104_1, u1ehi3, u2elo0]
                              · obtain ⟨p104_0, p104_1, p104_2, p104_3⟩ := h104c
                                linarith only [hlam, p104_0]
                        · linarith only [h6, h7, h74, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h73, hlam, hphi, ht12, u1ehi1, u2elo4]
                    · linarith only [h71, h72, hlam, hphi, ht12, u1ehi2, u2elo3]
                  · linarith only [h71, hlam, hphi, ht12, u1ehi1, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
                · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
                        · linarith only [h1, h138, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                            · linarith only [h0, h1, h135, h141, h6, hlam, hphi, ht12, u1ehi2, u2elo0]
                            · rcases h0bigk with h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [hlam, p143_0]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h0, h136, h141, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p143_1]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi2]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h138, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi2]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi4]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h0, hlam, p143_0]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [hlam, p143_0]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi2]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h138, h2, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi2]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h3, hlam, hphi, ht12, p143_1, u1ehi4, u2elo0]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h1, hlam, p143_0]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h6, hc02, hc34, hlam, hphi, ht23, p143_1]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [hlam, p143_0]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h6, hlam, p143_1]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h3, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi4]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h2, hlam, p143_0]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h4, hlam, p143_0]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h1, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi2]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [hlam, p143_0]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h3, h4, hlam, hphi, ht12, p143_1, u1ehi4, u2elo0]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h3, hlam, p143_0]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h5, hlam, p143_1]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h1, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p143_1, u1ehi2]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [h134, hlam, p143_1]
                              · obtain ⟨p143_0, p143_1, p143_2, p143_3⟩ := h143c
                                linarith only [hlam, p143_0]
                          · linarith only [h134, h138, h140, h4, hlam, hphi, ht12, u1ehi2, u2elo0]
                      · linarith only [h137, hlam, hphi, ht12, u1ehi1, u2elo4]
                    · linarith only [h135, h136, hlam, hphi, ht12, u1ehi2, u2elo3]
                  · linarith only [h135, hlam, hphi, ht12, u1ehi1, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h174 | h174
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h175 | h175
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h176 | h176
                        · linarith only [h1, h176, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h178 | h178
                          · linarith only [h134, h178, h2, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h180 | h180
                            · linarith only [h1, h180, h6, hlam, hphi, ht12, u1ehi2, u2elo2]
                            · rcases h0bigk with h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [hlam, p182_0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h0, h174, h180, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p182_1]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p182_1, u1ehi2]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h176, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p182_1, u1ehi2]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h134, h176, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p182_1, u1ehi2]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h0, hlam, p182_0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [hlam, p182_0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p182_1, u1ehi2]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h176, h2, hlam, hphi, ht12, p182_1, u1ehi2, u2elo0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h134, h176, h2, hlam, hphi, ht12, p182_1, u1ehi2, u2elo0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h1, hlam, p182_0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h6, hc02, hc34, hlam, hphi, ht23, p182_1]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [hlam, p182_0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h6, hlam, p182_1]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h134, h6, hlam, p182_1]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h2, hlam, p182_0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h4, hlam, p182_0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h134, hc03, hc45, hlam, hphi, ht34, p182_1]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [hlam, p182_0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h134, hlam, p182_0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h3, hlam, p182_0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h5, hlam, p182_1]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h1, h5, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p182_1, u1ehi2]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p182_1, u2elo0]
                              · obtain ⟨p182_0, p182_1, p182_2, p182_3⟩ := h182c
                                linarith only [hlam, p182_0]
                      · linarith only [h175, hlam, hphi, ht12, u1ehi1, u2elo4]
                    · linarith only [h173, h174, hlam, hphi, ht12, u1ehi2, u2elo3]
                  · linarith only [h173, hlam, hphi, ht12, u1ehi1, u2elo2]
            · linarith only [h0, h5, hlam, hphi, ht12, u1ehi1, u2elo4]
          · linarith only [h0, h4, hlam, hphi, ht12, u1ehi1, u2elo3]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h1, h2, hc14, hlam, hphi, u1ehi2]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · linarith only [h0, hlam, hphi, ht12, u1ehi0, u2elo1]

theorem n7l_sAA2_H_I_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h2ehi := hb2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
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
                      · linarith only [h15, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · linarith only [h15, h5, hlam]
                    · linarith only [h14, h9, hlam, p0_1]
                  · linarith only [h13, h7, hlam, p0_1]
                · linarith only [h12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h11, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
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
                        · linarith only [h36, h38, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h41 | h41
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
                                    · linarith only [h40, h45, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                    · linarith only [h40, h42, h45, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                  · linarith only [h38, h40, h42, h44, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
                                · linarith only [h36, h43, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
                                  · linarith only [h42, h50, h51, hc23, hlam, hphi, ht12, u1ehi3]
                                  · linarith only [h38, h51, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                · linarith only [h40, h50, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                            · linarith only [h30, h41, hlam]
                          · linarith only [h28, h40, hlam]
                    · linarith only [h35, hc15, hlam, hphi, p0_1, u1ehi2]
                  · linarith only [h28, h34, hlam, p0_1]
                · linarith only [h33, hlam, p0_0]
              · linarith only [h32, hc12, hlam, hphi, p0_1, u1ehi2]
    · linarith only [h23, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
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
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
                      · linarith only [h63, h75, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                        · linarith only [h63, h77, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                          · linarith only [h65, h79, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                                · linarith only [h75, h79, h83, hc23, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h75, h83, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h69, h82, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                                · linarith only [h75, h79, h88, hc23, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h75, h88, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h69, h87, hlam]
                    · linarith only [h74, hc15, hlam, hphi, p0_1, u1ehi3]
                  · linarith only [h73, hlam, p0_0]
                · linarith only [h72, hc13, hlam, hphi, p0_1, u1ehi3]
              · linarith only [h71, hc12, hlam, hphi, p0_1, u1ehi3]
    · linarith only [h62, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h97 | h97
    · rcases p0_3 (m.d 1 2) (by simp) with h98 | h98
      · linarith only [h98, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h100 | h100
        · linarith only [h100, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h102 | h102
          · linarith only [h102, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h104 | h104
            · linarith only [h104, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h106 | h106
              · rcases m.htr 0 1 3 (by decide) (by decide) with h107 | h107
                · rcases m.htr 0 1 4 (by decide) (by decide) with h108 | h108
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h109 | h109
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
                      · linarith only [h110, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
                        · linarith only [h100, h110, h112, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                            · linarith only [h100, h115, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                              · linarith only [h102, h117, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h120 | h120
                                  · linarith only [h112, h117, h119, h120, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h112, h120, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                · linarith only [h114, h115, h119, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h124 | h124
                            · linarith only [h100, h124, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h126 | h126
                              · linarith only [h102, h126, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                                · linarith only [h110, h114, h128, hc23, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h110, h128, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h109, hlam, p0_0]
                  · linarith only [h108, hc14, hlam, hphi, p0_1, u1ehi4]
                · linarith only [h102, h107, hc13, hlam, hphi, p0_1, u1ehi3]
              · linarith only [h102, h106, hc12, hlam, hphi, p0_1, u1ehi3]
    · linarith only [h97, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_H_I_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h2elo := hb2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, u1elo0]
  · linarith only [h0, hlam, ht01, ht12, u2elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h3 | h3
    · rcases m.htr 0 1 3 (by decide) (by decide) with h4 | h4
      · linarith only [h0, h4, hlam, ht01, u1elo0]
      · linarith only [h0, h4, hlam, ht01, u1elo2]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h7 | h7
      · linarith only [h0, h3, h7, hlam, ht01, u1elo1]
      · linarith only [h0, h7, hlam, ht01, u1elo2]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h10 | h10
    · rcases m.htr 0 1 3 (by decide) (by decide) with h11 | h11
      · rcases m.htr 0 1 4 (by decide) (by decide) with h12 | h12
        · linarith only [h0, h12, hlam, ht01, u1elo0]
        · linarith only [h0, h12, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h15 | h15
        · linarith only [h0, h11, h15, hlam, ht01, u1elo2]
        · linarith only [h0, h15, hlam, ht01, u1elo3]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h18 | h18
      · rcases m.htr 0 1 4 (by decide) (by decide) with h19 | h19
        · linarith only [h0, h10, h19, hlam, ht01, ht12, u2elo1]
        · linarith only [h0, h19, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h22 | h22
        · linarith only [h0, h10, h22, hlam, ht01, ht12, u2elo1]
        · linarith only [h0, h22, hlam, ht01, u1elo3]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h25 | h25
    · rcases m.htr 0 1 3 (by decide) (by decide) with h26 | h26
      · rcases m.htr 0 1 4 (by decide) (by decide) with h27 | h27
        · rcases m.htr 0 1 5 (by decide) (by decide) with h28 | h28
          · linarith only [h0, h28, hlam, ht01, u1elo0]
          · linarith only [h0, h28, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h31 | h31
          · linarith only [h0, h27, h31, hlam, ht01, u1elo3]
          · linarith only [h0, h31, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h34 | h34
        · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
          · linarith only [h0, h26, h35, hlam, ht01, u1elo2]
          · linarith only [h0, h35, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h38 | h38
          · linarith only [h0, h26, h38, hlam, ht01, u1elo2]
          · linarith only [h0, h38, hlam, ht01, u1elo4]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h41 | h41
      · rcases m.htr 0 1 4 (by decide) (by decide) with h42 | h42
        · rcases m.htr 0 1 5 (by decide) (by decide) with h43 | h43
          · linarith only [h0, h25, h43, hlam, ht01, u1elo1]
          · linarith only [h0, h43, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h46 | h46
          · linarith only [h0, h25, h46, hlam, ht01, ht12, u2elo1]
          · linarith only [h0, h46, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h49 | h49
        · rcases m.htr 0 1 5 (by decide) (by decide) with h50 | h50
          · linarith only [h0, h25, h50, hlam, ht01, ht12, u2elo1]
          · linarith only [h0, h50, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h53 | h53
          · linarith only [h0, h25, h53, hlam, ht01, ht12, u2elo1]
          · linarith only [h0, h53, hlam, ht01, u1elo4]

theorem n7l_sAA2_H_I_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_H_I_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, u1elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, ht01, u1elo0]
    · linarith only [h0, h2, hlam, ht01, u1elo1]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 1 3 (by decide) (by decide) with h6 | h6
      · linarith only [h0, h6, hlam, ht01, u1elo0]
      · linarith only [h5, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi1]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h9 | h9
      · linarith only [h0, h5, h9, hlam, ht01, u1elo1]
      · linarith only [h0, h9, hlam, ht01, u1elo2]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
    · rcases m.htr 0 1 3 (by decide) (by decide) with h13 | h13
      · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
        · linarith only [h0, h14, hlam, ht01, u1elo0]
        · linarith only [h12, h14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi1]
      · linarith only [h12, h13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi1]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h18 | h18
      · rcases m.htr 0 1 4 (by decide) (by decide) with h19 | h19
        · linarith only [h0, h12, h19, hlam, ht01, u1elo1]
        · linarith only [h0, h19, hlam, ht01, u1elo3]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h22 | h22
        · linarith only [h0, h12, h22, hlam, ht01, u1elo1]
        · linarith only [h0, h22, hlam, ht01, u1elo3]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h25 | h25
    · rcases m.htr 0 1 3 (by decide) (by decide) with h26 | h26
      · rcases m.htr 0 1 4 (by decide) (by decide) with h27 | h27
        · rcases m.htr 0 1 5 (by decide) (by decide) with h28 | h28
          · linarith only [h0, h28, hlam, ht01, u1elo0]
          · linarith only [h25, h28, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4, u2ehi1]
        · linarith only [h25, h27, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi1]
      · linarith only [h25, h26, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi1]
    · rcases m.htr 0 1 3 (by decide) (by decide) with h33 | h33
      · rcases m.htr 0 1 4 (by decide) (by decide) with h34 | h34
        · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
          · linarith only [h0, h25, h35, hlam, ht01, u1elo1]
          · linarith only [h0, h35, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h38 | h38
          · linarith only [h0, h25, h38, hlam, ht01, u1elo1]
          · linarith only [h0, h38, hlam, ht01, u1elo4]
      · rcases m.htr 0 1 4 (by decide) (by decide) with h41 | h41
        · rcases m.htr 0 1 5 (by decide) (by decide) with h42 | h42
          · linarith only [h0, h25, h42, hlam, ht01, u1elo1]
          · linarith only [h0, h42, hlam, ht01, u1elo4]
        · rcases m.htr 0 1 5 (by decide) (by decide) with h45 | h45
          · linarith only [h0, h25, h45, hlam, ht01, u1elo1]
          · linarith only [h0, h45, hlam, ht01, u1elo4]

theorem n7l_sAA2_H_I_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi8 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi8, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo3]

theorem n7l_sAA2_H_I_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_H_I_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_H_L_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1emin := hb1.2.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h2, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
          · linarith only [h1, h2, h6, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
            · linarith only [h1, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases h1emin with h10 | h10 | h10 | h10 | h10
              · linarith only [h10, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0]
              · linarith only [h1, h10, h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0]
              · linarith only [h1, h10, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0]
              · linarith only [h10, h4, hlam, ht12, u2elo3]
              · linarith only [h10, h6, hlam, ht12, u2elo4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
      · linarith only [h0, h1, h16, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
      · linarith only [h0, h1, h16, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h19 | h19
    · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
      · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
        · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
          · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
            · linarith only [h0, h19, h23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
            · rcases h1emin with h25 | h25 | h25 | h25 | h25
              · linarith only [h0, h25, hlam, ht12, u2elo1]
              · linarith only [h25, hlam, ht12, u2elo1]
              · linarith only [h0, h19, h25, hlam, ht12, u2elo1]
              · linarith only [h21, h25, hlam, ht12, u2elo1]
              · linarith only [h22, h25, hlam, ht12, u2elo1]
          · linarith only [h0, h19, h20, h22, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
        · linarith only [h0, h19, h20, h21, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
      · linarith only [h0, h20, hc01, hlam, hphi, ht12, u2elo2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
      · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
        · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
          · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
            · rcases h1emin with h38 | h38 | h38 | h38 | h38
              · linarith only [h38, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0]
              · linarith only [h38, hlam, ht12, u2elo1]
              · linarith only [h34, h38, hlam, ht12, u2elo1]
              · linarith only [h35, h38, hlam, ht12, u2elo1]
              · linarith only [h36, h38, hlam, ht12, u2elo1]
            · rcases h1emin with h44 | h44 | h44 | h44 | h44
              · linarith only [h19, h35, h37, h44, hlam, ht12, u2elo1]
              · linarith only [h44, hlam, ht12, u2elo1]
              · linarith only [h35, h37, h44, hlam, ht12, u2elo1]
              · linarith only [h35, h44, hlam, ht12, u2elo1]
              · linarith only [h36, h44, hlam, ht12, u2elo1]
          · linarith only [h0, h36, hc01, hlam, hphi, ht12, u2elo4]
        · linarith only [h19, h34, h35, hc01, hlam, hphi, ht12, u2elo3]
      · linarith only [h0, h34, hc01, hlam, hphi, ht12, u2elo2]

theorem n7l_sAA2_H_L_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_H_L_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · linarith only [h20, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h20, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h28 | h28
    · linarith only [h28, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h28, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_H_L_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2elo := hb2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
          · linarith only [h1, h3, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
            · linarith only [h1, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
              · linarith only [h2, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                · linarith only [h11, h3, h7, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                  · linarith only [h13, h3, h7, h9, hc12, hlam, hphi, u2elo3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h11, h13, h15, h3, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h11, h15, h3, hc12, hc45, hlam, hphi, ht23, ht34]
      · linarith only [h2, hc01, hlam, hphi, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA2_H_L_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h2bigk := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h0, h3, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h0, h10, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h13 | h13
              · linarith only [h13, h3, h5, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                · linarith only [h0, h15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h0, h15, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h18 | h18
            · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                · linarith only [h0, h20, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h2, h20, h3, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                · linarith only [h0, h23, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h2, h23, h3, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h26 | h26
              · linarith only [h18, h26, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
                · linarith only [h0, h28, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h2, h28, h3, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h31 | h31
          · rcases m.htr 0 2 5 (by decide) (by decide) with h32 | h32
            · rcases m.htr 0 3 5 (by decide) (by decide) with h33 | h33
              · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
                · linarith only [h3, h34, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                  · linarith only [h1, h34, h36, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h31, h36, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h3, h32, h33, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
              · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                · linarith only [h3, h41, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                  · linarith only [h0, h43, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h31, h43, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                · linarith only [h0, h46, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
                  · linarith only [h1, h46, h48, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h3, h31, h48, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h51 | h51
            · rcases m.htr 0 3 5 (by decide) (by decide) with h52 | h52
              · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
                · linarith only [h3, h53, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                  · linarith only [h1, h31, h51, h53, h55, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h57 | h57
                    · linarith only [h1, h53, h57, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h51, h57, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h3, h51, h52, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h61 | h61
              · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
                · linarith only [h3, h62, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                  · linarith only [h0, h31, h64, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h66 | h66
                    · linarith only [h0, h51, h66, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h68 | h68
                      · linarith only [h1, h68, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                        · linarith only [h2, h70, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h74 | h74
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h75 | h75
                                · linarith only [h62, h68, h70, h72, h75, hc12, hc23, hlam, hphi]
                                · linarith only [h62, h68, h74, h75, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                                · linarith only [h0, h31, h74, h78, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h1, h61, h62, h68, h78, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h1, h61, h73, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h83 | h83
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h84 | h84
                                · linarith only [h1, h61, h62, h68, h70, h84, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                                · linarith only [h3, h61, h72, h83, h84, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h72, h82, h83, hlam]
                            · linarith only [h3, h61, h82, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
                · linarith only [h0, h3, h89, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
                  · linarith only [h0, h91, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
                    · linarith only [h1, h51, h89, h93, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h95 | h95
                      · linarith only [h1, h95, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h97 | h97
                        · linarith only [h2, h97, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h100 | h100
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h101 | h101
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h102 | h102
                                · linarith only [h102, h89, h95, h97, h99, hc12, hc23, hlam, hphi]
                                · linarith only [h101, h102, h89, h95, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                                · linarith only [h0, h101, h105, h31, hc12, hc34, hlam, hphi, ht23]
                                · rcases h2bigk with h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p107_1, u0elo1]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h3, hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h31, hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h51, hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h0, hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h89, hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h91, hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h93, hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    rcases p107_3 (m.d 0 2) (by simp) with h118 | h118
                                    · linarith only [h118, hlam, p107_0]
                                    · rcases p107_3 (m.d 1 2) (by simp) with h120 | h120
                                      · linarith only [h120, h89, hlam]
                                      · rcases p107_3 (m.d 2 3) (by simp) with h122 | h122
                                        · rcases p107_3 (m.d 2 4) (by simp) with h123 | h123
                                          · linarith only [h123, h99, hlam]
                                          · linarith only [h123, h31, hlam]
                                        · linarith only [h122, hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    rcases p107_3 (m.d 0 2) (by simp) with h127 | h127
                                    · linarith only [h127, h3, hlam]
                                    · linarith only [h0, h127, hlam]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h89, h95, h99, hc12, hc23, hlam, hphi, p107_1]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h1, h100, h61, h89, hc12, hc23, hlam, hphi, p107_1]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h101, hc02, hc45, hlam, hphi, ht23, ht34, p107_1]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h101, hc12, hc45, hlam, hphi, ht23, ht34, p107_1]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h99, hlam, p107_1]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h101, hlam, p107_1]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    rcases p107_3 (m.d 0 2) (by simp) with h138 | h138
                                    · linarith only [h138, hlam, p107_0]
                                    · rcases p107_3 (m.d 1 2) (by simp) with h140 | h140
                                      · linarith only [h140, h93, hlam]
                                      · rcases p107_3 (m.d 2 3) (by simp) with h142 | h142
                                        · rcases p107_3 (m.d 2 4) (by simp) with h143 | h143
                                          · linarith only [h101, h143, hlam]
                                          · linarith only [h143, h31, hlam]
                                        · linarith only [h142, h3, hlam]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    rcases p107_3 (m.d 0 2) (by simp) with h147 | h147
                                    · linarith only [h147, h51, hlam]
                                    · linarith only [h0, h147, hlam]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h100, hlam, p107_0]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [h0, h31, hc12, hc25, hlam, hphi, p107_1]
                                  · obtain ⟨p107_0, p107_1, p107_2, p107_3⟩ := h107c
                                    linarith only [hlam, p107_0]
                            · linarith only [h100, h89, h95, h99, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h154 | h154
                            · linarith only [h1, h154, h61, h89, h99, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h156 | h156
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h157 | h157
                                · rcases h2bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p158_1, u0elo1]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h3, hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h31, hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h51, hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h0, hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h89, hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h91, hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h93, hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h154, h157, hc02, hc34, hlam, hphi, ht23, p158_1]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h154, h157, hc12, hc34, hlam, hphi, ht23, p158_1]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h99, hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h154, hlam, p158_1]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    rcases p158_3 (m.d 0 2) (by simp) with h174 | h174
                                    · linarith only [h174, hlam, p158_0]
                                    · rcases p158_3 (m.d 1 2) (by simp) with h176 | h176
                                      · linarith only [h176, h91, hlam]
                                      · rcases p158_3 (m.d 2 3) (by simp) with h178 | h178
                                        · linarith only [h178, h99, hlam]
                                        · linarith only [h178, h3, hlam]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    rcases p158_3 (m.d 0 2) (by simp) with h181 | h181
                                    · linarith only [h181, h31, hlam]
                                    · linarith only [h0, h181, hlam]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h0, h3, h99, hc12, hc34, hlam, hphi, ht23, p158_1]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h0, h51, h99, hc12, hc34, hlam, hphi, ht23, p158_1]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    rcases p158_3 (m.d 0 2) (by simp) with h187 | h187
                                    · linarith only [h187, hlam, p158_0]
                                    · rcases p158_3 (m.d 1 2) (by simp) with h189 | h189
                                      · linarith only [h189, h93, hlam]
                                      · rcases p158_3 (m.d 2 3) (by simp) with h191 | h191
                                        · linarith only [h154, h191, hlam]
                                        · linarith only [h191, h3, hlam]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    rcases p158_3 (m.d 0 2) (by simp) with h194 | h194
                                    · linarith only [h194, h51, hlam]
                                    · linarith only [h0, h194, hlam]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h0, h3, hc12, hc25, hlam, hphi, p158_1]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [h156, hlam, p158_0]
                                  · obtain ⟨p158_0, p158_1, p158_2, p158_3⟩ := h158c
                                    linarith only [hlam, p158_0]
                                · linarith only [h0, h157, h3, h99, hc12, hc45, hlam, hphi, ht23, ht34]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
                                · linarith only [h0, h156, h201, h31, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h201, h3, h99, hc12, hc45, hlam, hphi, ht23, ht34]
      · linarith only [h2, hc01, hlam, hphi, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA2_H_L_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA2_H_L_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_H_L_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_H_L_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_H_L_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
  · linarith only [h0, hlam, hphi, ht12, u1ehi0, u2elo1]

theorem n7l_sAA2_H_L_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h1ehi := hb1.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
            · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
              · linarith only [h4, h8, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h4, h5, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2, h4, h5, h7, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
          · linarith only [h0, h6, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
          · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
            · linarith only [h13, h14, h2, h5, hc12, hlam, hphi, u1ehi0]
            · linarith only [h14, h2, hc35, hlam, hphi, ht12, ht23, u1ehi0]
          · linarith only [h13, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h18 | h18
        · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
          · linarith only [h0, h19, h4, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h19, hc23, hlam, hphi, ht12, u1ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
          · linarith only [h0, h22, h4, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h22, hc23, hlam, hphi, ht12, u1ehi0]

theorem n7l_sAA2_H_L_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
      · linarith only [h0, h2, h4, hc12, hlam, hphi, u1ehi0]
      · linarith only [h0, h4, hc23, hlam, hphi, ht12, u1ehi0]

theorem n7l_sAA2_H_L_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_H_L_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hlam, hphi, p0_1, u1elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hlam, hphi, p0_1, u1elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hlam, hphi, p0_1, u1elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hlam, hphi, p0_1, u1elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_H_L_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · linarith only [h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
      · linarith only [h0, h2, h3, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h6 | h6
      · linarith only [h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h8 | h8
        · linarith only [h6, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h10 | h10
          · rcases m.htr 0 4 5 (by decide) (by decide) with h11 | h11
            · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
              · linarith only [h0, h12, h6, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
                · linarith only [h14, h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h10, h20, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h10, h11, h20, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h0, h10, h11, h14, h19, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h18, h6, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h10, h11, h17, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h10, h16, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
              · linarith only [h27, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                · linarith only [h27, h29, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                    · linarith only [h11, h31, h32, h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                        · linarith only [h29, h32, h35, hc24, hlam, hphi, u2ehi1]
                        · linarith only [h35, h8, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h10, h34, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h10, h31, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h40 | h40
            · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
              · linarith only [h41, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                · linarith only [h41, h43, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                  · linarith only [h10, h2, h45, hc01, hlam, hphi, u1elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                      · linarith only [h41, h45, h48, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h48, h6, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h0, h40, h41, h45, h47, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
              · linarith only [h52, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
                · linarith only [h52, h54, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h10, h56, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
                    · linarith only [h40, h58, h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                      · linarith only [h10, h6, h60, hc23, hlam, hphi, u2ehi0]
                      · linarith only [h6, h60, hc34, hlam, hphi, ht23, u2ehi0]

theorem n7l_sAA2_H_L_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_H_L_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_H_L_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_H_R_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAA2_H_R_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1bigk := hb1.1
  have h2ehi := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                        · rcases h1bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h11, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h11, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi2]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h11, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h1, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h6, hlam, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h11, h7, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h0, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h2, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h7, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h9, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h8, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi4]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h3, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h8, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p12_1]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [h10, hlam, p12_0]
                          · obtain ⟨p12_0, p12_1, p12_2, p12_3⟩ := h12c
                            linarith only [hlam, p12_0]
                        · linarith only [h1, h10, h11, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h39 | h39
                        · linarith only [h0, h10, h39, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c | h41c
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [hlam, p41_0]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p41_1, u2ehi1]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p41_1, u2ehi2]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p41_1, u2ehi3]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h10, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p41_1, u2ehi3]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h0, hlam, p41_0]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [hlam, p41_0]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p41_1]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p41_1, u2ehi3]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h0, h10, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p41_1, u2ehi3]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h1, hlam, p41_0]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h6, hlam, p41_1]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [hlam, p41_0]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h7, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p41_1, u2ehi3]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h0, h10, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p41_1, u2ehi3]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h2, hlam, p41_0]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h7, hlam, p41_0]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h9, hlam, p41_0]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [hlam, p41_0]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h10, hlam, p41_1]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h3, hlam, p41_0]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h8, hlam, p41_0]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p41_1]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [h0, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p41_1, u2ehi3]
                          · obtain ⟨p41_0, p41_1, p41_2, p41_3⟩ := h41c
                            linarith only [hlam, p41_0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                        · rcases h1bigk with h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [hlam, p69_0]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u2ehi1]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u2ehi2]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u2ehi2]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u2ehi4]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h0, hlam, p69_0]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [hlam, p69_0]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p69_1, u2ehi2]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h0, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u2ehi2]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p69_1]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h1, hlam, p69_0]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h6, hlam, p69_1]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [hlam, p69_0]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h9, hlam, p69_1]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h8, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p69_1, u2ehi4]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h2, hlam, p69_0]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h7, hlam, p69_0]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p69_1]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [hlam, p69_0]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h0, h4, h5, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u2ehi4]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h3, hlam, p69_0]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h8, hlam, p69_0]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h6, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p69_1, u2ehi2]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [h67, hlam, p69_0]
                          · obtain ⟨p69_0, p69_1, p69_2, p69_3⟩ := h69c
                            linarith only [hlam, p69_0]
                        · linarith only [h0, h4, h5, h67, h68, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                        · linarith only [h0, h67, h7, h96, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [hlam, p98_0]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p98_1, u2ehi1]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p98_1, u2ehi2]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p98_1, u2ehi2]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h8, h96, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p98_1, u2ehi3]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h0, hlam, p98_0]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [hlam, p98_0]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p98_1, u2ehi2]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h0, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p98_1, u2ehi2]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p98_1]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h1, hlam, p98_0]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h6, hlam, p98_1]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [hlam, p98_0]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h9, hlam, p98_1]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h67, h9, hlam, p98_1]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h2, hlam, p98_0]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h7, hlam, p98_0]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h6, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p98_1, u2ehi2]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [hlam, p98_0]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h67, hlam, p98_1]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h3, hlam, p98_0]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h8, hlam, p98_0]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h0, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p98_1, u2ehi2]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [h0, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                          · obtain ⟨p98_0, p98_1, p98_2, p98_3⟩ := h98c
                            linarith only [hlam, p98_0]
                  · linarith only [h6, h8, hc25, hlam, hphi, u2ehi2]
                · linarith only [h6, h7, hc24, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h126 | h126
                · linarith only [h126, h6, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h128 | h128
                  · linarith only [h0, h128, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h130 | h130
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h132 | h132
                        · rcases h1bigk with h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [hlam, p133_0]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p133_1, u2ehi1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h128, h130, h131, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p133_1, u2ehi1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h128, h131, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p133_1, u2ehi1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h128, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p133_1, u2ehi1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h0, hlam, p133_0]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [hlam, p133_0]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h6, hlam, p133_0]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h126, hlam, p133_1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h128, hlam, p133_1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h1, hlam, p133_0]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p133_1, u2ehi1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [hlam, p133_0]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h0, h128, h131, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p133_1, u2ehi1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h0, h128, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p133_1, u2ehi1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h2, hlam, p133_0]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p133_1, u2ehi1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h130, hlam, p133_0]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [hlam, p133_0]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h0, h128, h130, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p133_1, u2ehi1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h3, hlam, p133_0]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p133_1, u2ehi1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h130, h131, hlam, p133_1]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [h131, hlam, p133_0]
                          · obtain ⟨p133_0, p133_1, p133_2, p133_3⟩ := h133c
                            linarith only [hlam, p133_0]
                        · linarith only [h126, h131, h132, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                        · linarith only [h126, h131, h160, hc24, hlam, hphi, u2ehi1]
                        · linarith only [h126, h160, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h164 | h164
                        · rcases h1bigk with h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [hlam, p165_0]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p165_1, u2ehi1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p165_1, u2ehi1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h163, hc01, hc45, hlam, hphi, ht0b, ht5b, p165_1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h128, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p165_1, u2ehi1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h0, hlam, p165_0]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [hlam, p165_0]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h6, hlam, p165_0]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h126, hlam, p165_1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h128, hlam, p165_1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h1, hlam, p165_0]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p165_1, u2ehi1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [hlam, p165_0]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h130, hlam, p165_1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h128, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p165_1, u2ehi1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h2, hlam, p165_0]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p165_1, u2ehi1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h0, h130, h4, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p165_1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [hlam, p165_0]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h0, h128, h130, h4, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p165_1, u2ehi1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h3, hlam, p165_0]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p165_1, u2ehi1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h0, h130, h163, h4, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p165_1, u2ehi1]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [h163, hlam, p165_0]
                          · obtain ⟨p165_0, p165_1, p165_2, p165_3⟩ := h165c
                            linarith only [hlam, p165_0]
                        · linarith only [h126, h164, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h192 | h192
                        · linarith only [h126, h163, h192, hc24, hlam, hphi, u2ehi1]
                        · linarith only [h126, h192, hc45, hlam, hphi, ht23, ht34, u2ehi1]
            · linarith only [h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
          · linarith only [h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h3, hc15, hlam, hphi, ht01, u0ehi0]
      · linarith only [h0, h2, hc14, hlam, hphi, ht01, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n7l_sAA2_H_R_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA2_H_R_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA2_H_R_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA2_H_R_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAA2_H_R_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h10, h13, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h10, h12, h13, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                            · linarith only [h0, h12, h16, h5, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases h2bigk with h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h0, h5, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p18_1, u1ehi4]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                rcases p18_3 (m.d 0 2) (by simp) with h21 | h21
                                · rcases p18_3 (m.d 1 2) (by simp) with h22 | h22
                                  · linarith only [h0, h22, hlam]
                                  · linarith only [h22, h5, hlam]
                                · linarith only [h21, hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                rcases p18_3 (m.d 0 2) (by simp) with h26 | h26
                                · rcases p18_3 (m.d 1 2) (by simp) with h27 | h27
                                  · linarith only [h0, h27, hlam]
                                  · linarith only [h27, h6, hlam]
                                · linarith only [h26, hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                rcases p18_3 (m.d 0 2) (by simp) with h31 | h31
                                · rcases p18_3 (m.d 1 2) (by simp) with h32 | h32
                                  · linarith only [h0, h32, hlam]
                                  · linarith only [h32, h7, hlam]
                                · linarith only [h31, hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h0, hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h0, h11, hc01, hc35, hlam, hphi, ht0b, ht5b, p18_1]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                rcases p18_3 (m.d 0 2) (by simp) with h39 | h39
                                · rcases p18_3 (m.d 1 2) (by simp) with h40 | h40
                                  · rcases p18_3 (m.d 2 3) (by simp) with h41 | h41
                                    · linarith only [h41, h5, hlam]
                                    · linarith only [h10, h41, hlam]
                                  · linarith only [h40, hlam, p18_0]
                                · linarith only [h2, h39, hlam]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                rcases p18_3 (m.d 0 2) (by simp) with h46 | h46
                                · rcases p18_3 (m.d 1 2) (by simp) with h47 | h47
                                  · rcases p18_3 (m.d 2 3) (by simp) with h48 | h48
                                    · linarith only [h48, h5, hlam]
                                    · linarith only [h11, h48, hlam]
                                  · linarith only [h47, hlam, p18_0]
                                · linarith only [h3, h46, hlam]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h1, hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h5, hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h0, h10, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h0, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p18_1]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h2, hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h6, hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h10, hlam, p18_1]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h12, hlam, p18_1]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h3, hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h7, hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h11, hlam, p18_0]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [h0, h10, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                              · obtain ⟨p18_0, p18_1, p18_2, p18_3⟩ := h18c
                                linarith only [hlam, p18_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                          · linarith only [h10, h11, h68, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h70 | h70
                            · linarith only [h0, h5, h68, h70, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h10, h11, h5, h70, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
                        · linarith only [h0, h10, h5, h73, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
                            · rcases h2bigk with h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h5, h8, h9, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p77_1, u1ehi4]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                rcases p77_3 (m.d 0 2) (by simp) with h80 | h80
                                · rcases p77_3 (m.d 1 2) (by simp) with h81 | h81
                                  · linarith only [h0, h81, hlam]
                                  · linarith only [h5, h81, hlam]
                                · linarith only [h80, hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                rcases p77_3 (m.d 0 2) (by simp) with h85 | h85
                                · rcases p77_3 (m.d 1 2) (by simp) with h86 | h86
                                  · linarith only [h0, h86, hlam]
                                  · linarith only [h6, h86, hlam]
                                · linarith only [h85, hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                rcases p77_3 (m.d 0 2) (by simp) with h90 | h90
                                · rcases p77_3 (m.d 1 2) (by simp) with h91 | h91
                                  · linarith only [h0, h91, hlam]
                                  · linarith only [h7, h91, hlam]
                                · linarith only [h90, hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h0, hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                rcases p77_3 (m.d 0 2) (by simp) with h97 | h97
                                · rcases p77_3 (m.d 1 2) (by simp) with h98 | h98
                                  · rcases p77_3 (m.d 2 3) (by simp) with h99 | h99
                                    · linarith only [h99, hlam, p77_0]
                                    · rcases p77_3 (m.d 2 4) (by simp) with h101 | h101
                                      · linarith only [h101, h6, hlam]
                                      · linarith only [h10, h101, hlam]
                                  · linarith only [h98, hlam, p77_0]
                                · linarith only [h1, h97, hlam]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h0, h75, hc01, hc45, hlam, hphi, ht0b, ht5b, p77_1]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                rcases p77_3 (m.d 0 2) (by simp) with h107 | h107
                                · rcases p77_3 (m.d 1 2) (by simp) with h108 | h108
                                  · rcases p77_3 (m.d 2 3) (by simp) with h109 | h109
                                    · linarith only [h109, h5, hlam]
                                    · rcases p77_3 (m.d 2 4) (by simp) with h111 | h111
                                      · linarith only [h111, h6, hlam]
                                      · linarith only [h111, h75, hlam]
                                  · linarith only [h108, hlam, p77_0]
                                · linarith only [h107, h3, hlam]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h1, hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h5, hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h10, hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h73, hlam, p77_1]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h2, hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h6, hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p77_1]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h0, h10, h5, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p77_1]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h3, hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h7, hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p77_1]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [h75, hlam, p77_0]
                              · obtain ⟨p77_0, p77_1, p77_2, p77_3⟩ := h77c
                                linarith only [hlam, p77_0]
                            · linarith only [h0, h10, h5, h76, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h132 | h132
                            · linarith only [h0, h132, h5, h75, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h10, h132, h5, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
                  · linarith only [h8, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                · linarith only [h7, hc25, hlam, hphi, ht12, u1ehi1]
              · linarith only [h5, h6, hc24, hlam, hphi, ht12, u1ehi2]
            · linarith only [h5, hc23, hlam, hphi, ht12, u1ehi1]
          · linarith only [h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc25, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h1, h2, hc24, hlam, hphi, ht01, ht12, u0ehi2]
    · linarith only [h1, hc23, hlam, hphi, ht01, ht12, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA2_H_R_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h1, h6, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h1, h6, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h3, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h0, h1, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h0, h1, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
          · linarith only [h4, hc35, hlam, hphi, ht12, ht23, u1ehi2]
        · linarith only [h3, hc34, hlam, hphi, ht12, ht23, u1ehi2]
      · linarith only [h2, hc25, hlam, hphi, ht12, u1ehi1]
    · linarith only [h1, hc23, hlam, hphi, ht12, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA2_H_R_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAA2_H_R_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h2ehi := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
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
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h17 | h17
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
                              · linarith only [h19, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                              · linarith only [h19, h5, hlam]
                            · linarith only [h18, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                          · linarith only [h17, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h16, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h15, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h14, h9, hlam, p0_1]
                  · linarith only [h13, h7, hlam, p0_1]
                · linarith only [h12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h11, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h31 | h31
    · rcases p0_3 (m.d 1 2) (by simp) with h32 | h32
      · linarith only [h32, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h34 | h34
        · linarith only [h34, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h36 | h36
          · linarith only [h36, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h38 | h38
            · linarith only [h38, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h40 | h40
              · rcases m.htr 0 1 3 (by decide) (by decide) with h41 | h41
                · rcases m.htr 0 1 4 (by decide) (by decide) with h42 | h42
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h43 | h43
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h44 | h44
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h45 | h45
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h46 | h46
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h47 | h47
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
                              · linarith only [h32, h48, hlam]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
                                · linarith only [h48, h50, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
                                  · linarith only [h48, h52, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi4]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h55 | h55
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h57 | h57
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h58 | h58
                                            · rcases m.htr 2 4 5 (by decide) (by decide) with h59 | h59
                                              · rcases m.htr 3 4 5 (by decide) (by decide) with h60 | h60
                                                · linarith only [h54, h60, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                                · linarith only [h54, h56, h60, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                              · linarith only [h54, h56, h59, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                            · linarith only [h50, h55, h57, h58, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
                                          · linarith only [h48, h57, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                                            · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                                              · linarith only [h50, h56, h66, h68, hc23, hlam, hphi, ht12, u1ehi1]
                                              · linarith only [h45, h47, h50, h68, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                            · linarith only [h55, h67, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                                          · linarith only [h48, h54, h66, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
                                      · linarith only [h38, h55, hlam]
                                    · linarith only [h36, h54, hlam]
                            · linarith only [h47, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                          · linarith only [h46, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h45, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h44, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h43, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h36, h42, hlam, p0_1]
                · linarith only [h41, hlam, p0_0]
              · linarith only [h40, hc12, hlam, hphi, p0_1, u1ehi2]
    · linarith only [h31, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h84 | h84
    · rcases p0_3 (m.d 1 2) (by simp) with h85 | h85
      · linarith only [h85, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h87 | h87
        · linarith only [h87, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
          · linarith only [h89, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h91 | h91
            · linarith only [h91, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h93 | h93
              · rcases m.htr 0 1 3 (by decide) (by decide) with h94 | h94
                · rcases m.htr 0 1 4 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h97 | h97
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h98 | h98
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h99 | h99
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                              · linarith only [h101, h85, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                                · linarith only [h103, h85, hlam]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                                  · linarith only [h101, h105, h93, h97, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
                                    · linarith only [h107, h87, hlam]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h109 | h109
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                                          · linarith only [h105, h107, h109, h111, h93, h97, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                          · linarith only [h101, h111, h93, h97, h98, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                        · linarith only [h110, h91, hlam]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                                          · linarith only [h101, h107, h116, hc23, hlam, hphi, ht12, u1ehi1]
                                          · linarith only [h101, h116, h93, h97, h98, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                        · linarith only [h115, h91, hlam]
                            · linarith only [h100, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                          · linarith only [h99, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h98, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h97, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h96, hc15, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h95, hlam, p0_0]
                · linarith only [h87, h94, hlam, p0_1]
              · linarith only [h93, hc12, hlam, hphi, ht01, u0ehi0]
    · linarith only [h84, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h129 | h129
    · rcases p0_3 (m.d 1 2) (by simp) with h130 | h130
      · linarith only [h130, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h132 | h132
        · linarith only [h132, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h134 | h134
          · linarith only [h134, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h136 | h136
            · linarith only [h136, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h138 | h138
              · rcases m.htr 0 1 3 (by decide) (by decide) with h139 | h139
                · rcases m.htr 0 1 4 (by decide) (by decide) with h140 | h140
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h141 | h141
                    · rcases m.htr 0 2 3 (by decide) (by decide) with h142 | h142
                      · rcases m.htr 0 3 4 (by decide) (by decide) with h143 | h143
                        · rcases m.htr 0 3 5 (by decide) (by decide) with h144 | h144
                          · rcases m.htr 0 4 5 (by decide) (by decide) with h145 | h145
                            · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
                              · linarith only [h130, h146, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                              · rcases m.htr 1 2 4 (by decide) (by decide) with h148 | h148
                                · linarith only [h138, h142, h146, h148, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
                                  · linarith only [h130, h150, hlam]
                                  · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                                      · linarith only [h132, h153, hlam]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h155 | h155
                                        · linarith only [h134, h155, hlam]
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h157 | h157
                                          · rcases m.htr 2 3 5 (by decide) (by decide) with h158 | h158
                                            · linarith only [h138, h142, h148, h152, h153, h158, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                            · linarith only [h138, h142, h144, h146, h158, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                                          · linarith only [h146, h152, h157, hc13, hlam, hphi, u1ehi1]
                                    · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                                      · linarith only [h132, h162, hlam]
                                      · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                                        · linarith only [h134, h164, hlam]
                                        · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                                          · linarith only [h146, h152, h166, hc23, hlam, hphi, ht12, u1ehi1]
                                          · linarith only [h138, h142, h143, h146, h166, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · linarith only [h145, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                          · linarith only [h144, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · linarith only [h143, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                      · linarith only [h142, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h141, hlam, p0_0]
                  · linarith only [h134, h140, hlam, p0_1]
                · linarith only [h139, hc13, hlam, hphi, ht01, u0ehi0]
              · linarith only [h130, h138, hlam, p0_1]
    · linarith only [h129, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_H_R_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA2_H_R_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA2_H_R_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA2_H_R_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA2_H_R_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA2_H_R_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA2_M_IR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi2, u2elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi3, u2elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi4, u2elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_IR_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_IR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0ehi := hb0.2.1
  have h1bigk := hb1.1
  have h2ehi := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h3 | h3
    · rcases p0_3 (m.d 1 2) (by simp) with h4 | h4
      · rcases p0_3 (m.d 1 3) (by simp) with h5 | h5
        · linarith only [h5, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 1 5) (by simp) with h8 | h8
            · rcases m.htr 0 1 2 (by decide) (by decide) with h9 | h9
              · linarith only [h4, h9, hlam]
              · linarith only [h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h12 | h12
              · linarith only [h12, h4, hlam]
              · linarith only [h12, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h15 | h15
            · rcases m.htr 0 1 2 (by decide) (by decide) with h16 | h16
              · linarith only [h16, h4, hlam]
              · linarith only [h16, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h19 | h19
              · linarith only [h19, h4, hlam]
              · linarith only [h19, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
      · linarith only [h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
    · linarith only [h3, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h24 | h24
    · rcases p0_3 (m.d 1 2) (by simp) with h25 | h25
      · rcases p0_3 (m.d 1 3) (by simp) with h26 | h26
        · rcases p0_3 (m.d 1 4) (by simp) with h27 | h27
          · linarith only [h27, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h29 | h29
            · rcases m.htr 0 1 2 (by decide) (by decide) with h30 | h30
              · linarith only [h25, h30, hlam]
              · linarith only [h30, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h33 | h33
              · linarith only [h25, h33, hlam]
              · linarith only [h33, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h36 | h36
          · linarith only [h36, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h38 | h38
            · rcases m.htr 0 1 2 (by decide) (by decide) with h39 | h39
              · linarith only [h25, h39, hlam]
              · linarith only [h26, h39, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h42 | h42
              · linarith only [h25, h42, hlam]
              · linarith only [h26, h42, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
      · linarith only [h25, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
    · linarith only [h24, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h47 | h47
    · rcases p0_3 (m.d 1 2) (by simp) with h48 | h48
      · rcases p0_3 (m.d 1 3) (by simp) with h49 | h49
        · rcases p0_3 (m.d 1 4) (by simp) with h50 | h50
          · rcases p0_3 (m.d 1 5) (by simp) with h51 | h51
            · linarith only [h51, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h53 | h53
              · linarith only [h48, h53, hlam]
              · linarith only [h53, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h56 | h56
            · linarith only [h56, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h58 | h58
              · linarith only [h48, h58, hlam]
              · linarith only [h50, h58, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · rcases p0_3 (m.d 1 4) (by simp) with h61 | h61
          · rcases p0_3 (m.d 1 5) (by simp) with h62 | h62
            · linarith only [h62, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h64 | h64
              · linarith only [h48, h64, hlam]
              · linarith only [h49, h64, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h67 | h67
            · linarith only [h67, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h69 | h69
              · linarith only [h48, h69, hlam]
              · linarith only [h49, h69, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
      · linarith only [h48, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
    · linarith only [h47, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h76 | h76
    · rcases p0_3 (m.d 1 2) (by simp) with h77 | h77
      · rcases p0_3 (m.d 1 3) (by simp) with h78 | h78
        · linarith only [h78, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h80 | h80
          · rcases p0_3 (m.d 1 5) (by simp) with h81 | h81
            · rcases m.htr 0 1 2 (by decide) (by decide) with h82 | h82
              · linarith only [h82, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h76, h82, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h85 | h85
              · linarith only [h85, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h76, h85, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h88 | h88
            · rcases m.htr 0 1 2 (by decide) (by decide) with h89 | h89
              · linarith only [h89, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h76, h89, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h92 | h92
              · linarith only [h92, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h76, h92, hlam]
      · linarith only [h77, hlam, p0_0]
    · linarith only [h76, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h97 | h97
    · rcases p0_3 (m.d 1 2) (by simp) with h98 | h98
      · rcases p0_3 (m.d 1 3) (by simp) with h99 | h99
        · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
          · linarith only [h100, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h102 | h102
            · rcases m.htr 0 1 2 (by decide) (by decide) with h103 | h103
              · linarith only [h103, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h103, h97, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h106 | h106
              · linarith only [h106, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h106, h97, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h109 | h109
          · linarith only [h109, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h111 | h111
            · rcases m.htr 0 1 2 (by decide) (by decide) with h112 | h112
              · linarith only [h112, h99, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h112, h97, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h115 | h115
              · linarith only [h115, h99, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h115, h97, hlam]
      · linarith only [h98, hlam, p0_0]
    · linarith only [h97, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h120 | h120
    · rcases p0_3 (m.d 1 2) (by simp) with h121 | h121
      · rcases p0_3 (m.d 1 3) (by simp) with h122 | h122
        · rcases p0_3 (m.d 1 4) (by simp) with h123 | h123
          · rcases p0_3 (m.d 1 5) (by simp) with h124 | h124
            · linarith only [h124, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h126 | h126
              · linarith only [h126, hc01, hc15, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h120, h126, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h129 | h129
            · linarith only [h129, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h131 | h131
              · linarith only [h123, h131, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h120, h131, hlam]
        · rcases p0_3 (m.d 1 4) (by simp) with h134 | h134
          · rcases p0_3 (m.d 1 5) (by simp) with h135 | h135
            · linarith only [h135, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h137 | h137
              · linarith only [h122, h137, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h120, h137, hlam]
          · rcases p0_3 (m.d 1 5) (by simp) with h140 | h140
            · linarith only [h140, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h142 | h142
              · linarith only [h122, h142, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h120, h142, hlam]
      · linarith only [h121, hlam, p0_0]
    · linarith only [h120, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h150 | h150
    · rcases p0_3 (m.d 1 2) (by simp) with h151 | h151
      · rcases p0_3 (m.d 1 3) (by simp) with h152 | h152
        · rcases p0_3 (m.d 1 4) (by simp) with h153 | h153
          · linarith only [h153, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h155 | h155
            · rcases m.htr 0 1 2 (by decide) (by decide) with h156 | h156
              · linarith only [h151, h156, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h150, h156, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h159 | h159
              · linarith only [h151, h159, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h150, h159, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h152, hlam, p0_0]
      · linarith only [h150, h151, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
    · linarith only [h150, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h165 | h165
    · rcases p0_3 (m.d 1 2) (by simp) with h166 | h166
      · rcases p0_3 (m.d 1 3) (by simp) with h167 | h167
        · rcases p0_3 (m.d 1 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 1 5) (by simp) with h169 | h169
            · linarith only [h169, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h171 | h171
              · linarith only [h166, h171, hc01, hc15, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h165, h171, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · rcases p0_3 (m.d 1 5) (by simp) with h174 | h174
            · linarith only [h174, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h176 | h176
              · linarith only [h166, h168, h176, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h165, h168, h176, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
        · linarith only [h167, hlam, p0_0]
      · linarith only [h165, h166, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
    · linarith only [h165, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h184 | h184
    · rcases p0_3 (m.d 1 2) (by simp) with h185 | h185
      · rcases p0_3 (m.d 1 3) (by simp) with h186 | h186
        · linarith only [h186, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h188 | h188
          · rcases p0_3 (m.d 1 5) (by simp) with h189 | h189
            · rcases m.htr 0 1 2 (by decide) (by decide) with h190 | h190
              · linarith only [h185, h190, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h184, h190, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h193 | h193
              · linarith only [h185, h193, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h184, h193, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · linarith only [h188, hlam, p0_0]
      · linarith only [h184, h185, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
    · linarith only [h184, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h200 | h200
    · rcases p0_3 (m.d 1 2) (by simp) with h201 | h201
      · rcases p0_3 (m.d 1 3) (by simp) with h202 | h202
        · rcases p0_3 (m.d 1 4) (by simp) with h203 | h203
          · rcases p0_3 (m.d 1 5) (by simp) with h204 | h204
            · linarith only [h204, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h206 | h206
              · linarith only [h201, h206, hc01, hc15, hlam, hphi, ht0b, ht5b, p0_1]
              · linarith only [h200, h206, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p0_1]
          · linarith only [h203, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h210 | h210
          · rcases p0_3 (m.d 1 5) (by simp) with h211 | h211
            · linarith only [h211, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h213 | h213
              · linarith only [h201, h202, h213, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h200, h202, h213, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
          · linarith only [h210, hlam, p0_0]
      · linarith only [h200, h201, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
    · linarith only [h200, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h221 | h221
    · rcases p0_3 (m.d 1 2) (by simp) with h222 | h222
      · rcases p0_3 (m.d 1 3) (by simp) with h223 | h223
        · linarith only [h223, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 1 5) (by simp) with h226 | h226
            · rcases m.htr 0 1 2 (by decide) (by decide) with h227 | h227
              · linarith only [h222, h227, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h221, h227, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h226, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h231 | h231
            · rcases m.htr 0 1 2 (by decide) (by decide) with h232 | h232
              · linarith only [h222, h232, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h221, h232, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h231, hlam, p0_0]
      · linarith only [h221, h222, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
    · linarith only [h221, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h238 | h238
    · rcases p0_3 (m.d 1 2) (by simp) with h239 | h239
      · rcases p0_3 (m.d 1 3) (by simp) with h240 | h240
        · rcases p0_3 (m.d 1 4) (by simp) with h241 | h241
          · linarith only [h241, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h243 | h243
            · rcases m.htr 0 1 2 (by decide) (by decide) with h244 | h244
              · linarith only [h239, h244, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1]
              · linarith only [h238, h244, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1]
            · linarith only [h243, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h248 | h248
          · linarith only [h248, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h250 | h250
            · rcases m.htr 0 1 2 (by decide) (by decide) with h251 | h251
              · linarith only [h239, h240, h251, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
              · linarith only [h238, h240, h251, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p0_1]
            · linarith only [h250, hlam, p0_0]
      · linarith only [h238, h239, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
    · linarith only [h238, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_IR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA2_M_IR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA2_M_IR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi0, u1elo0]

theorem n7l_sAA2_M_IR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  linarith only [hlam, hphi, ht12, u1ehi1, u2elo1]

theorem n7l_sAA2_M_IR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_IR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h2, h5, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h2, h5, h6, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h2, h3, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
            · linarith only [h0, h2, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
          · linarith only [h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
        · linarith only [h3, hc34, hlam, hphi, ht12, ht23, u1ehi2]
      · linarith only [h2, hc23, hlam, hphi, ht12, u1ehi1]
    · linarith only [h1, hc15, hlam, hphi, u1ehi0]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem n7l_sAA2_M_IR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi2, u2elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi3, u2elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, p0_1, u0ehi4, u2elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_IR_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_IR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h2ehi := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
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
                · rcases m.htr 0 1 5 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                    · linarith only [h14, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                    · linarith only [h14, h5, hlam]
                  · linarith only [h13, h9, hlam, p0_1]
                · linarith only [h12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
              · linarith only [h11, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 2) (by simp) with h22 | h22
      · linarith only [h22, hc12, hlam, hphi, p0_1, u1ehi2]
      · rcases p0_3 (m.d 1 3) (by simp) with h24 | h24
        · linarith only [h24, hlam, p0_0]
        · rcases p0_3 (m.d 1 4) (by simp) with h26 | h26
          · linarith only [h26, hc14, hlam, hphi, p0_1, u1ehi2]
          · rcases p0_3 (m.d 1 5) (by simp) with h28 | h28
            · linarith only [h28, hc15, hlam, hphi, p0_1, u1ehi2]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h30 | h30
              · rcases m.htr 0 1 3 (by decide) (by decide) with h31 | h31
                · rcases m.htr 0 1 5 (by decide) (by decide) with h32 | h32
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
                    · linarith only [h22, h33, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
                      · linarith only [h33, h35, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
                        · linarith only [h33, h37, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h39 | h39
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h41 | h41
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
                                      · linarith only [h39, h45, hc01, hc45, hlam, hphi, ht0b, ht5b, p0_1]
                                      · linarith only [h39, h41, h45, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                    · linarith only [h39, h41, h44, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p0_1]
                                  · linarith only [h35, h40, h42, h43, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
                                · linarith only [h33, h42, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                                    · linarith only [h41, h51, h53, hc23, hlam, hphi, ht12, u1ehi3]
                                    · linarith only [h35, h53, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                  · linarith only [h40, h52, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1]
                                · linarith only [h33, h39, h51, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
                            · linarith only [h28, h40, hlam]
                          · linarith only [h26, h39, hlam]
                  · linarith only [h32, hc15, hlam, hphi, p0_1, u1ehi2]
                · linarith only [h31, hlam, p0_0]
              · linarith only [h30, hc12, hlam, hphi, p0_1, u1ehi2]
    · linarith only [h21, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h64 | h64
    · rcases p0_3 (m.d 1 2) (by simp) with h65 | h65
      · linarith only [h65, hc12, hlam, hphi, p0_1, u1ehi3]
      · rcases p0_3 (m.d 1 3) (by simp) with h67 | h67
        · linarith only [h67, hc13, hlam, hphi, p0_1, u1ehi3]
        · rcases p0_3 (m.d 1 4) (by simp) with h69 | h69
          · linarith only [h69, hlam, p0_0]
          · rcases p0_3 (m.d 1 5) (by simp) with h71 | h71
            · linarith only [h71, hc15, hlam, hphi, p0_1, u1ehi3]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h73 | h73
              · rcases m.htr 0 1 3 (by decide) (by decide) with h74 | h74
                · rcases m.htr 0 1 5 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                    · linarith only [h65, h76, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                      · linarith only [h65, h78, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                        · linarith only [h67, h76, h80, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                          · linarith only [h67, h82, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                                · linarith only [h80, h82, h84, h86, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h76, h86, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h71, h85, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                                · linarith only [h76, h82, h91, hc23, hlam, hphi, ht12, u1ehi1]
                                · linarith only [h76, h91, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h71, h90, hlam]
                  · linarith only [h75, hc15, hlam, hphi, p0_1, u1ehi3]
                · linarith only [h74, hc13, hlam, hphi, p0_1, u1ehi3]
              · linarith only [h73, hc12, hlam, hphi, p0_1, u1ehi3]
    · linarith only [h64, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h99 | h99
    · rcases p0_3 (m.d 1 2) (by simp) with h100 | h100
      · linarith only [h100, hc12, hlam, hphi, p0_1, u1ehi4]
      · rcases p0_3 (m.d 1 3) (by simp) with h102 | h102
        · linarith only [h102, hc13, hlam, hphi, p0_1, u1ehi4]
        · rcases p0_3 (m.d 1 4) (by simp) with h104 | h104
          · linarith only [h104, hc14, hlam, hphi, p0_1, u1ehi4]
          · rcases p0_3 (m.d 1 5) (by simp) with h106 | h106
            · linarith only [h106, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h108 | h108
              · rcases m.htr 0 1 3 (by decide) (by decide) with h109 | h109
                · rcases m.htr 0 1 5 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
                    · linarith only [h100, h111, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                      · linarith only [h102, h111, h113, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                        · linarith only [h100, h115, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                            · linarith only [h102, h118, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                              · linarith only [h104, h120, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h123 | h123
                                  · linarith only [h113, h117, h118, h123, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h111, h123, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                                · linarith only [h111, h117, h118, h122, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h127 | h127
                            · linarith only [h102, h127, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h129 | h129
                              · linarith only [h104, h129, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
                                · linarith only [h117, h131, hc23, hlam, hphi, ht12, u1ehi2]
                                · linarith only [h111, h131, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h110, hlam, p0_0]
                · linarith only [h109, hc13, hlam, hphi, p0_1, u1ehi4]
              · linarith only [h108, hc12, hlam, hphi, p0_1, u1ehi4]
    · linarith only [h99, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_IR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0emin := hb0.1
  have h0ehi := hb0.2.1
  have h1elo := hb1.1
  have h2elo := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases h0emin with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, u1elo0]
        · linarith only [h3, hlam, ht01, ht12, u2elo0]
        · linarith only [h2, h3, hlam, ht01, ht12, u2elo0]
        · linarith only [h0, h3, hlam, ht01, u1elo0]
        · linarith only [h1, h3, hlam, ht01, u1elo0]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
    · linarith only [h1, hlam, hphi, ht01, u0ehi0, u1elo4]
  · linarith only [h0, hlam, hphi, ht01, u0ehi0, u1elo3]

theorem n7l_sAA2_M_IR_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_M_IR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u1elo0, u2ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, p0_1, u0ehi2, u1elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, p0_1, u0ehi3, u1elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, p0_1, u0ehi4, u1elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_IR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_M_IR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_M_IR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_M_LI_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h12 | h12
    · linarith only [h12, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h12, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h16 | h16
    · linarith only [h16, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h16, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h19 | h19
    · linarith only [h19, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h19, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h26 | h26
    · linarith only [h26, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h26, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h30 | h30
    · linarith only [h30, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h30, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h34, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_LI_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_LI_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · linarith only [h20, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h20, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h28 | h28
    · linarith only [h28, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h28, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_LI_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  rcases h0emin with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, u1elo0]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, ht01, u1elo0]
    · linarith only [h2, hc01, hlam, hphi, u1elo1]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 1 3 (by decide) (by decide) with h6 | h6
      · linarith only [h0, h6, hlam, ht01, u1elo0]
      · linarith only [h6, hc01, hlam, hphi, u1elo2]
    · linarith only [h5, hc01, hlam, hphi, u1elo1]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h10 | h10
    · rcases m.htr 0 1 3 (by decide) (by decide) with h11 | h11
      · rcases m.htr 0 1 4 (by decide) (by decide) with h12 | h12
        · linarith only [h0, h12, hlam, ht01, u1elo0]
        · linarith only [h12, hc01, hlam, hphi, u1elo3]
      · linarith only [h10, h11, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
    · linarith only [h10, hc01, hlam, hphi, u1elo1]
  · rcases m.htr 0 1 2 (by decide) (by decide) with h17 | h17
    · rcases m.htr 0 1 3 (by decide) (by decide) with h18 | h18
      · rcases m.htr 0 1 4 (by decide) (by decide) with h19 | h19
        · rcases m.htr 0 1 5 (by decide) (by decide) with h20 | h20
          · linarith only [h0, h20, hlam, ht01, u1elo0]
          · linarith only [h20, hc01, hlam, hphi, u1elo4]
        · linarith only [h17, h19, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
      · linarith only [h17, h18, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
    · linarith only [h17, hc01, hlam, hphi, u1elo1]

theorem n7l_sAA2_M_LI_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_M_LI_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
  · linarith only [h0, hc01, hlam, hphi, u1elo2]

theorem n7l_sAA2_M_LI_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  linarith only [hlam, hphi, ht12, u1ehi1, u2elo1]

theorem n7l_sAA2_M_LI_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_M_LI_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
  · linarith only [h0, hc14, hlam, hphi, u1ehi0]

theorem n7l_sAA2_M_LI_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht12, p0_1, u1ehi2, u2elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht12, p0_1, u1ehi3, u2elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht12, p0_1, u1ehi4, u2elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_LI_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1ehi := hb1.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases m.htr 0 1 2 (by decide) (by decide) with h8 | h8
              · linarith only [h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h8, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · linarith only [h11, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h11, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · rcases m.htr 0 1 2 (by decide) (by decide) with h15 | h15
              · linarith only [h15, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h15, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h18 | h18
              · linarith only [h18, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h18, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · rcases m.htr 0 1 2 (by decide) (by decide) with h23 | h23
              · linarith only [h23, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h23, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h26 | h26
              · linarith only [h26, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h26, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · rcases m.htr 0 1 2 (by decide) (by decide) with h30 | h30
              · linarith only [h30, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h30, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h33 | h33
              · linarith only [h33, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h33, hlam, p0_0]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · rcases p0_3 (m.d 0 2) (by simp) with h38 | h38
      · rcases p0_3 (m.d 0 3) (by simp) with h39 | h39
        · linarith only [h39, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h41 | h41
          · rcases p0_3 (m.d 0 5) (by simp) with h42 | h42
            · rcases m.htr 0 1 2 (by decide) (by decide) with h43 | h43
              · linarith only [h38, h43, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h45 | h45
                · linarith only [h43, h45, hc12, hlam, hphi, u1ehi2]
                · linarith only [h45, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h48 | h48
              · linarith only [h38, h48, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h50 | h50
                · linarith only [h48, h50, hc12, hlam, hphi, u1ehi2]
                · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h53 | h53
            · rcases m.htr 0 1 2 (by decide) (by decide) with h54 | h54
              · linarith only [h38, h54, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h56 | h56
                · linarith only [h54, h56, hc12, hlam, hphi, u1ehi2]
                · linarith only [h56, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h59 | h59
              · linarith only [h38, h59, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h61 | h61
                · linarith only [h59, h61, hc12, hlam, hphi, u1ehi2]
                · linarith only [h61, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h64 | h64
        · linarith only [h64, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h66 | h66
          · rcases p0_3 (m.d 0 5) (by simp) with h67 | h67
            · rcases m.htr 0 1 2 (by decide) (by decide) with h68 | h68
              · linarith only [h38, h68, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h38, h68, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h71 | h71
              · linarith only [h38, h71, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h38, h71, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h74 | h74
            · rcases m.htr 0 1 2 (by decide) (by decide) with h75 | h75
              · linarith only [h38, h75, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h38, h75, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h78 | h78
              · linarith only [h38, h78, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h38, h78, hlam, p0_1]
    · linarith only [h37, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h82 | h82
    · rcases p0_3 (m.d 0 2) (by simp) with h83 | h83
      · rcases p0_3 (m.d 0 3) (by simp) with h84 | h84
        · rcases p0_3 (m.d 0 4) (by simp) with h85 | h85
          · linarith only [h85, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h87 | h87
            · rcases m.htr 0 1 2 (by decide) (by decide) with h88 | h88
              · linarith only [h83, h88, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h90 | h90
                · linarith only [h84, h90, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h92 | h92
                  · linarith only [h90, h92, hc13, hlam, hphi, u1ehi3]
                  · linarith only [h92, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h95 | h95
              · linarith only [h83, h95, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h97 | h97
                · linarith only [h84, h97, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h99 | h99
                  · linarith only [h95, h99, hc12, hlam, hphi, u1ehi3]
                  · linarith only [h99, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h102 | h102
          · linarith only [h102, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h104 | h104
            · rcases m.htr 0 1 2 (by decide) (by decide) with h105 | h105
              · linarith only [h105, h83, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h107 | h107
                · linarith only [h105, h107, hc12, hlam, hphi, u1ehi2]
                · linarith only [h107, h84, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h110 | h110
              · linarith only [h110, h83, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h112 | h112
                · linarith only [h110, h112, hc12, hlam, hphi, u1ehi2]
                · linarith only [h112, h84, hlam, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h115 | h115
        · rcases p0_3 (m.d 0 4) (by simp) with h116 | h116
          · linarith only [h116, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h118 | h118
            · rcases m.htr 0 1 2 (by decide) (by decide) with h119 | h119
              · linarith only [h119, h83, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h119, h83, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h122 | h122
              · linarith only [h122, h83, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h122, h83, hlam, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h125 | h125
          · linarith only [h125, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h127 | h127
            · rcases m.htr 0 1 2 (by decide) (by decide) with h128 | h128
              · linarith only [h128, h83, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h128, h83, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h131 | h131
              · linarith only [h131, h83, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h131, h83, hlam, p0_1]
    · linarith only [h82, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h135 | h135
    · rcases p0_3 (m.d 0 2) (by simp) with h136 | h136
      · rcases p0_3 (m.d 0 3) (by simp) with h137 | h137
        · rcases p0_3 (m.d 0 4) (by simp) with h138 | h138
          · rcases p0_3 (m.d 0 5) (by simp) with h139 | h139
            · linarith only [h139, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h141 | h141
              · linarith only [h136, h141, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h143 | h143
                · linarith only [h137, h143, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h145 | h145
                  · linarith only [h138, h145, hlam]
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h147 | h147
                    · linarith only [h145, h147, hc14, hlam, hphi, u1ehi4]
                    · linarith only [h147, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h150 | h150
            · linarith only [h150, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h152 | h152
              · linarith only [h136, h152, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h154 | h154
                · linarith only [h137, h154, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h156 | h156
                  · linarith only [h152, h156, hc12, hlam, hphi, u1ehi3]
                  · linarith only [h138, h156, hlam, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 0 5) (by simp) with h160 | h160
            · linarith only [h160, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h162 | h162
              · linarith only [h136, h162, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h164 | h164
                · linarith only [h162, h164, hc12, hlam, hphi, u1ehi2]
                · linarith only [h137, h164, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h167 | h167
            · linarith only [h167, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h169 | h169
              · linarith only [h136, h169, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h171 | h171
                · linarith only [h169, h171, hc12, hlam, hphi, u1ehi2]
                · linarith only [h137, h171, hlam, p0_1]
      · rcases p0_3 (m.d 0 3) (by simp) with h174 | h174
        · rcases p0_3 (m.d 0 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 0 5) (by simp) with h176 | h176
            · linarith only [h176, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h178 | h178
              · linarith only [h136, h178, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h136, h178, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h181 | h181
            · linarith only [h181, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h183 | h183
              · linarith only [h136, h183, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h136, h183, hlam, p0_1]
        · rcases p0_3 (m.d 0 4) (by simp) with h186 | h186
          · rcases p0_3 (m.d 0 5) (by simp) with h187 | h187
            · linarith only [h187, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h189 | h189
              · linarith only [h136, h189, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h136, h189, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h192 | h192
            · linarith only [h192, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h194 | h194
              · linarith only [h136, h194, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h136, h194, hlam, p0_1]
    · linarith only [h135, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h200 | h200
    · rcases p0_3 (m.d 0 2) (by simp) with h201 | h201
      · rcases p0_3 (m.d 0 3) (by simp) with h202 | h202
        · linarith only [h202, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h204 | h204
          · rcases p0_3 (m.d 0 5) (by simp) with h205 | h205
            · rcases m.htr 0 1 2 (by decide) (by decide) with h206 | h206
              · rcases m.htr 0 1 3 (by decide) (by decide) with h207 | h207
                · linarith only [h206, h207, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
                · linarith only [h206, h207, hc13, hlam, hphi, u1ehi1]
              · linarith only [h200, h206, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h211 | h211
              · rcases m.htr 0 1 3 (by decide) (by decide) with h212 | h212
                · linarith only [h212, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1, u1ehi2]
                · linarith only [h211, h212, hc13, hlam, hphi, u1ehi1]
              · linarith only [h200, h211, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h216 | h216
            · rcases m.htr 0 1 2 (by decide) (by decide) with h217 | h217
              · rcases m.htr 0 1 3 (by decide) (by decide) with h218 | h218
                · linarith only [h217, h218, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
                · linarith only [h217, h218, hc13, hlam, hphi, u1ehi1]
              · linarith only [h200, h217, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h222 | h222
              · rcases m.htr 0 1 3 (by decide) (by decide) with h223 | h223
                · linarith only [h222, h223, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
                · linarith only [h222, h223, hc13, hlam, hphi, u1ehi1]
              · linarith only [h200, h222, hlam]
      · linarith only [h201, hlam, p0_0]
    · linarith only [h200, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h229 | h229
    · rcases p0_3 (m.d 0 2) (by simp) with h230 | h230
      · rcases p0_3 (m.d 0 3) (by simp) with h231 | h231
        · rcases p0_3 (m.d 0 4) (by simp) with h232 | h232
          · linarith only [h232, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h234 | h234
            · rcases m.htr 0 1 2 (by decide) (by decide) with h235 | h235
              · rcases m.htr 0 1 3 (by decide) (by decide) with h236 | h236
                · rcases m.htr 0 1 4 (by decide) (by decide) with h237 | h237
                  · linarith only [h235, h237, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi3]
                  · linarith only [h236, h237, hc14, hlam, hphi, u1ehi2]
                · linarith only [h235, h236, hc13, hlam, hphi, u1ehi1]
              · linarith only [h229, h235, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h242 | h242
              · rcases m.htr 0 1 3 (by decide) (by decide) with h243 | h243
                · rcases m.htr 0 1 4 (by decide) (by decide) with h244 | h244
                  · linarith only [h244, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1, u1ehi3]
                  · linarith only [h243, h244, hc14, hlam, hphi, u1ehi2]
                · linarith only [h242, h243, hc13, hlam, hphi, u1ehi1]
              · linarith only [h229, h242, hlam]
        · rcases p0_3 (m.d 0 4) (by simp) with h249 | h249
          · linarith only [h249, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h251 | h251
            · rcases m.htr 0 1 2 (by decide) (by decide) with h252 | h252
              · rcases m.htr 0 1 3 (by decide) (by decide) with h253 | h253
                · linarith only [h231, h252, h253, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
                · linarith only [h252, h253, hc13, hlam, hphi, u1ehi1]
              · linarith only [h229, h252, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h257 | h257
              · rcases m.htr 0 1 3 (by decide) (by decide) with h258 | h258
                · linarith only [h231, h258, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1, u1ehi2]
                · linarith only [h257, h258, hc13, hlam, hphi, u1ehi1]
              · linarith only [h229, h257, hlam]
      · linarith only [h230, hlam, p0_0]
    · linarith only [h229, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h264 | h264
    · rcases p0_3 (m.d 0 2) (by simp) with h265 | h265
      · rcases p0_3 (m.d 0 3) (by simp) with h266 | h266
        · rcases p0_3 (m.d 0 4) (by simp) with h267 | h267
          · rcases p0_3 (m.d 0 5) (by simp) with h268 | h268
            · linarith only [h268, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h270 | h270
              · rcases m.htr 0 1 3 (by decide) (by decide) with h271 | h271
                · rcases m.htr 0 1 4 (by decide) (by decide) with h272 | h272
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h273 | h273
                    · linarith only [h270, h273, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi4]
                    · linarith only [h271, h273, hc15, hlam, hphi, u1ehi2]
                  · linarith only [h271, h272, hc14, hlam, hphi, u1ehi2]
                · linarith only [h270, h271, hc13, hlam, hphi, u1ehi1]
              · linarith only [h264, h270, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h279 | h279
            · linarith only [h279, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h281 | h281
              · rcases m.htr 0 1 3 (by decide) (by decide) with h282 | h282
                · rcases m.htr 0 1 4 (by decide) (by decide) with h283 | h283
                  · linarith only [h267, h283, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1, u1ehi3]
                  · linarith only [h282, h283, hc14, hlam, hphi, u1ehi2]
                · linarith only [h281, h282, hc13, hlam, hphi, u1ehi1]
              · linarith only [h264, h281, hlam]
        · rcases p0_3 (m.d 0 4) (by simp) with h288 | h288
          · rcases p0_3 (m.d 0 5) (by simp) with h289 | h289
            · linarith only [h289, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h291 | h291
              · rcases m.htr 0 1 3 (by decide) (by decide) with h292 | h292
                · linarith only [h266, h292, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1, u1ehi2]
                · linarith only [h291, h292, hc13, hlam, hphi, u1ehi1]
              · linarith only [h264, h291, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h296 | h296
            · linarith only [h296, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h298 | h298
              · rcases m.htr 0 1 3 (by decide) (by decide) with h299 | h299
                · linarith only [h266, h299, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1, u1ehi2]
                · linarith only [h298, h299, hc13, hlam, hphi, u1ehi1]
              · linarith only [h264, h298, hlam]
      · linarith only [h265, hlam, p0_0]
    · linarith only [h264, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo2, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h306 | h306
    · rcases p0_3 (m.d 0 2) (by simp) with h307 | h307
      · linarith only [h307, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h309 | h309
        · rcases p0_3 (m.d 0 4) (by simp) with h310 | h310
          · rcases p0_3 (m.d 0 5) (by simp) with h311 | h311
            · rcases m.htr 0 1 2 (by decide) (by decide) with h312 | h312
              · linarith only [h312, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo2, u1ehi1]
              · linarith only [h306, h312, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h315 | h315
              · linarith only [h315, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo2, u1ehi1]
              · linarith only [h306, h315, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h318 | h318
            · rcases m.htr 0 1 2 (by decide) (by decide) with h319 | h319
              · linarith only [h306, h319, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h306, h319, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h322 | h322
              · linarith only [h306, h322, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h306, h322, hlam, p0_1]
        · linarith only [h309, hlam, p0_0]
    · linarith only [h306, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo2, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h328 | h328
    · rcases p0_3 (m.d 0 2) (by simp) with h329 | h329
      · rcases p0_3 (m.d 0 3) (by simp) with h330 | h330
        · rcases p0_3 (m.d 0 4) (by simp) with h331 | h331
          · linarith only [h331, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h333 | h333
            · rcases m.htr 0 1 2 (by decide) (by decide) with h334 | h334
              · rcases m.htr 0 1 3 (by decide) (by decide) with h335 | h335
                · rcases m.htr 0 1 4 (by decide) (by decide) with h336 | h336
                  · linarith only [h329, h334, h336, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi3]
                  · linarith only [h334, h336, hc14, hlam, hphi, u1ehi1]
                · linarith only [h328, h335, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h340 | h340
                · linarith only [h334, h340, hc12, hlam, hphi, u1ehi2]
                · linarith only [h328, h340, hlam]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h343 | h343
              · rcases m.htr 0 1 3 (by decide) (by decide) with h344 | h344
                · rcases m.htr 0 1 4 (by decide) (by decide) with h345 | h345
                  · linarith only [h344, h345, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi3]
                  · linarith only [h343, h345, hc14, hlam, hphi, u1ehi1]
                · linarith only [h328, h344, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h349 | h349
                · linarith only [h343, h349, hc12, hlam, hphi, u1ehi2]
                · linarith only [h328, h349, hlam]
        · linarith only [h330, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h353 | h353
        · rcases p0_3 (m.d 0 4) (by simp) with h354 | h354
          · linarith only [h354, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h356 | h356
            · rcases m.htr 0 1 2 (by decide) (by decide) with h357 | h357
              · linarith only [h329, h357, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo2, u1ehi1]
              · linarith only [h328, h329, h357, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h360 | h360
              · linarith only [h328, h329, h360, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h328, h329, h360, hlam, p0_1]
        · linarith only [h353, hlam, p0_0]
    · linarith only [h328, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo2, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h365 | h365
    · rcases p0_3 (m.d 0 2) (by simp) with h366 | h366
      · rcases p0_3 (m.d 0 3) (by simp) with h367 | h367
        · rcases p0_3 (m.d 0 4) (by simp) with h368 | h368
          · rcases p0_3 (m.d 0 5) (by simp) with h369 | h369
            · linarith only [h369, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h371 | h371
              · rcases m.htr 0 1 3 (by decide) (by decide) with h372 | h372
                · rcases m.htr 0 1 4 (by decide) (by decide) with h373 | h373
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h374 | h374
                    · linarith only [h366, h371, h374, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi4]
                    · linarith only [h371, h374, hc15, hlam, hphi, u1ehi1]
                  · linarith only [h371, h373, hc14, hlam, hphi, u1ehi1]
                · linarith only [h365, h372, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h379 | h379
                · linarith only [h371, h379, hc12, hlam, hphi, u1ehi2]
                · linarith only [h365, h379, hlam]
          · rcases p0_3 (m.d 0 5) (by simp) with h382 | h382
            · linarith only [h382, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h384 | h384
              · rcases m.htr 0 1 3 (by decide) (by decide) with h385 | h385
                · rcases m.htr 0 1 4 (by decide) (by decide) with h386 | h386
                  · linarith only [h368, h385, h386, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi3]
                  · linarith only [h384, h386, hc14, hlam, hphi, u1ehi1]
                · linarith only [h365, h385, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h390 | h390
                · linarith only [h384, h390, hc12, hlam, hphi, u1ehi2]
                · linarith only [h365, h390, hlam]
        · linarith only [h367, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h394 | h394
        · rcases p0_3 (m.d 0 4) (by simp) with h395 | h395
          · rcases p0_3 (m.d 0 5) (by simp) with h396 | h396
            · linarith only [h396, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h398 | h398
              · linarith only [h366, h398, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo2, u1ehi1]
              · linarith only [h365, h366, h398, hlam, p0_1]
          · rcases p0_3 (m.d 0 5) (by simp) with h401 | h401
            · linarith only [h401, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h403 | h403
              · linarith only [h365, h366, h403, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h365, h366, h403, hlam, p0_1]
        · linarith only [h394, hlam, p0_0]
    · linarith only [h365, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo2, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h409 | h409
    · rcases p0_3 (m.d 0 2) (by simp) with h410 | h410
      · linarith only [h410, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h412 | h412
        · rcases p0_3 (m.d 0 4) (by simp) with h413 | h413
          · rcases p0_3 (m.d 0 5) (by simp) with h414 | h414
            · rcases m.htr 0 1 2 (by decide) (by decide) with h415 | h415
              · linarith only [h415, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi1]
              · linarith only [h409, h415, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h418 | h418
              · linarith only [h409, h418, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h409, h418, hlam, p0_1]
          · linarith only [h413, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h422 | h422
          · rcases p0_3 (m.d 0 5) (by simp) with h423 | h423
            · rcases m.htr 0 1 2 (by decide) (by decide) with h424 | h424
              · linarith only [h424, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi1]
              · linarith only [h409, h424, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h427 | h427
              · linarith only [h409, h427, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h409, h427, hlam, p0_1]
          · linarith only [h422, hlam, p0_0]
    · linarith only [h409, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h432 | h432
    · rcases p0_3 (m.d 0 2) (by simp) with h433 | h433
      · rcases p0_3 (m.d 0 3) (by simp) with h434 | h434
        · linarith only [h434, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h436 | h436
          · rcases p0_3 (m.d 0 5) (by simp) with h437 | h437
            · rcases m.htr 0 1 2 (by decide) (by decide) with h438 | h438
              · rcases m.htr 0 1 3 (by decide) (by decide) with h439 | h439
                · linarith only [h433, h438, h439, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
                · linarith only [h438, h439, hc13, hlam, hphi, u1ehi1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h442 | h442
                · linarith only [h438, h442, hc12, hlam, hphi, u1ehi2]
                · linarith only [h442, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h445 | h445
              · rcases m.htr 0 1 3 (by decide) (by decide) with h446 | h446
                · linarith only [h433, h445, h446, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
                · linarith only [h445, h446, hc13, hlam, hphi, u1ehi1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h449 | h449
                · linarith only [h445, h449, hc12, hlam, hphi, u1ehi2]
                · linarith only [h449, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi0]
          · linarith only [h436, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h453 | h453
        · linarith only [h453, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h455 | h455
          · rcases p0_3 (m.d 0 5) (by simp) with h456 | h456
            · rcases m.htr 0 1 2 (by decide) (by decide) with h457 | h457
              · linarith only [h433, h457, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi1]
              · linarith only [h432, h433, h457, hlam, p0_1]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h460 | h460
              · linarith only [h433, h460, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi1]
              · linarith only [h432, h433, h460, hlam, p0_1]
          · linarith only [h455, hlam, p0_0]
    · linarith only [h432, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h466 | h466
    · rcases p0_3 (m.d 0 2) (by simp) with h467 | h467
      · rcases p0_3 (m.d 0 3) (by simp) with h468 | h468
        · rcases p0_3 (m.d 0 4) (by simp) with h469 | h469
          · rcases p0_3 (m.d 0 5) (by simp) with h470 | h470
            · linarith only [h470, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h472 | h472
              · rcases m.htr 0 1 3 (by decide) (by decide) with h473 | h473
                · rcases m.htr 0 1 4 (by decide) (by decide) with h474 | h474
                  · rcases m.htr 0 1 5 (by decide) (by decide) with h475 | h475
                    · linarith only [h467, h472, h475, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi4]
                    · linarith only [h472, h475, hc15, hlam, hphi, u1ehi1]
                  · linarith only [h466, h474, hlam]
                · linarith only [h472, h473, hc13, hlam, hphi, u1ehi1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h480 | h480
                · linarith only [h472, h480, hc12, hlam, hphi, u1ehi2]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h482 | h482
                  · linarith only [h472, h482, hc12, hlam, hphi, u1ehi3]
                  · linarith only [h466, h482, hlam]
          · linarith only [h469, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h486 | h486
          · rcases p0_3 (m.d 0 5) (by simp) with h487 | h487
            · linarith only [h487, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h489 | h489
              · rcases m.htr 0 1 3 (by decide) (by decide) with h490 | h490
                · linarith only [h468, h490, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi2]
                · linarith only [h489, h490, hc13, hlam, hphi, u1ehi1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h493 | h493
                · linarith only [h489, h493, hc12, hlam, hphi, u1ehi2]
                · linarith only [h468, h493, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi0]
          · linarith only [h486, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h497 | h497
        · rcases p0_3 (m.d 0 4) (by simp) with h498 | h498
          · rcases p0_3 (m.d 0 5) (by simp) with h499 | h499
            · linarith only [h499, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h501 | h501
              · linarith only [h467, h501, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi1]
              · linarith only [h466, h467, h501, hlam, p0_1]
          · linarith only [h498, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h505 | h505
          · rcases p0_3 (m.d 0 5) (by simp) with h506 | h506
            · linarith only [h506, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h508 | h508
              · linarith only [h467, h508, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi1]
              · linarith only [h466, h467, h508, hlam, p0_1]
          · linarith only [h505, hlam, p0_0]
    · linarith only [h466, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo4, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h514 | h514
    · rcases p0_3 (m.d 0 2) (by simp) with h515 | h515
      · linarith only [h515, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h517 | h517
        · rcases p0_3 (m.d 0 4) (by simp) with h518 | h518
          · rcases p0_3 (m.d 0 5) (by simp) with h519 | h519
            · rcases m.htr 0 1 2 (by decide) (by decide) with h520 | h520
              · linarith only [h520, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo4, u1ehi1]
              · linarith only [h514, h520, hlam, p0_1]
            · linarith only [h519, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h524 | h524
            · rcases m.htr 0 1 2 (by decide) (by decide) with h525 | h525
              · linarith only [h517, h525, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo2, u1ehi1]
              · linarith only [h514, h525, hlam, p0_1]
            · linarith only [h524, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h529 | h529
          · rcases p0_3 (m.d 0 5) (by simp) with h530 | h530
            · rcases m.htr 0 1 2 (by decide) (by decide) with h531 | h531
              · linarith only [h529, h531, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo3, u1ehi1]
              · linarith only [h514, h531, hlam, p0_1]
            · linarith only [h530, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h535 | h535
            · rcases m.htr 0 1 2 (by decide) (by decide) with h536 | h536
              · linarith only [h514, h536, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h514, h536, hlam, p0_1]
            · linarith only [h535, hlam, p0_0]
    · linarith only [h514, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo4, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h541 | h541
    · rcases p0_3 (m.d 0 2) (by simp) with h542 | h542
      · rcases p0_3 (m.d 0 3) (by simp) with h543 | h543
        · linarith only [h543, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h545 | h545
          · rcases p0_3 (m.d 0 5) (by simp) with h546 | h546
            · rcases m.htr 0 1 2 (by decide) (by decide) with h547 | h547
              · rcases m.htr 0 1 3 (by decide) (by decide) with h548 | h548
                · linarith only [h542, h547, h548, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
                · linarith only [h547, h548, hc13, hlam, hphi, u1ehi1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h551 | h551
                · linarith only [h547, h551, hc12, hlam, hphi, u1ehi2]
                · linarith only [h541, h551, hlam, p0_1]
            · linarith only [h546, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h555 | h555
            · rcases m.htr 0 1 2 (by decide) (by decide) with h556 | h556
              · rcases m.htr 0 1 3 (by decide) (by decide) with h557 | h557
                · linarith only [h542, h556, h557, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
                · linarith only [h556, h557, hc13, hlam, hphi, u1ehi1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h560 | h560
                · linarith only [h556, h560, hc12, hlam, hphi, u1ehi2]
                · linarith only [h560, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo4, u1ehi0]
            · linarith only [h555, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h564 | h564
        · linarith only [h564, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h566 | h566
          · rcases p0_3 (m.d 0 5) (by simp) with h567 | h567
            · rcases m.htr 0 1 2 (by decide) (by decide) with h568 | h568
              · linarith only [h542, h568, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo4, u1ehi1]
              · linarith only [h541, h542, h568, hlam, p0_1]
            · linarith only [h567, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h572 | h572
            · rcases m.htr 0 1 2 (by decide) (by decide) with h573 | h573
              · linarith only [h542, h573, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo4, u1ehi1]
              · linarith only [h541, h542, h573, hlam, p0_1]
            · linarith only [h572, hlam, p0_0]
    · linarith only [h541, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo4, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h578 | h578
    · rcases p0_3 (m.d 0 2) (by simp) with h579 | h579
      · rcases p0_3 (m.d 0 3) (by simp) with h580 | h580
        · rcases p0_3 (m.d 0 4) (by simp) with h581 | h581
          · linarith only [h581, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h583 | h583
            · rcases m.htr 0 1 2 (by decide) (by decide) with h584 | h584
              · rcases m.htr 0 1 3 (by decide) (by decide) with h585 | h585
                · rcases m.htr 0 1 4 (by decide) (by decide) with h586 | h586
                  · linarith only [h579, h584, h586, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi3]
                  · linarith only [h584, h586, hc14, hlam, hphi, u1ehi1]
                · linarith only [h584, h585, hc13, hlam, hphi, u1ehi1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h590 | h590
                · linarith only [h584, h590, hc12, hlam, hphi, u1ehi2]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h592 | h592
                  · linarith only [h584, h592, hc12, hlam, hphi, u1ehi3]
                  · linarith only [h592, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo4, u1ehi0]
            · linarith only [h583, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h596 | h596
          · linarith only [h596, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h598 | h598
            · rcases m.htr 0 1 2 (by decide) (by decide) with h599 | h599
              · rcases m.htr 0 1 3 (by decide) (by decide) with h600 | h600
                · linarith only [h579, h580, h599, h600, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
                · linarith only [h599, h600, hc13, hlam, hphi, u1ehi1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h603 | h603
                · linarith only [h599, h603, hc12, hlam, hphi, u1ehi2]
                · linarith only [h578, h580, h603, hlam, p0_1]
            · linarith only [h598, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h607 | h607
        · rcases p0_3 (m.d 0 4) (by simp) with h608 | h608
          · linarith only [h608, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h610 | h610
            · rcases m.htr 0 1 2 (by decide) (by decide) with h611 | h611
              · linarith only [h578, h579, h611, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h578, h579, h611, hlam, p0_1]
            · linarith only [h610, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h615 | h615
          · linarith only [h615, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h617 | h617
            · rcases m.htr 0 1 2 (by decide) (by decide) with h618 | h618
              · linarith only [h578, h579, h618, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
              · linarith only [h578, h579, h618, hlam, p0_1]
            · linarith only [h617, hlam, p0_0]
    · linarith only [h578, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo4, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_LI_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_LI_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h2ehi := hb2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
            · linarith only [h1, h4, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
              · linarith only [h1, h4, h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                · rcases h1bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [hlam, p11_0]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u1elo0, u2ehi1]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h4, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u1elo0, u2ehi1]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h10, hc45, hlam, hphi, ht01, ht0b, ht5b, p11_1, u1elo0]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u1elo0, u2ehi1]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h0, hlam, p11_0]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [hlam, p11_0]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h4, hlam, p11_0]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h6, hlam, p11_1]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h8, hlam, p11_1]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h1, hlam, p11_0]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u1elo2, u2ehi1]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [hlam, p11_0]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h1, h10, h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u1elo0, u2ehi1]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h1, h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u1elo0, u2ehi1]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h2, hlam, p11_0]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u1elo3, u2ehi1]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11_1, u1elo0]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [hlam, p11_0]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h2, h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u1elo0, u2ehi1]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h3, hlam, p11_0]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u1elo4, u2ehi1]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h10, h2, h4, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u1elo0, u2ehi1]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [h10, hlam, p11_0]
                  · obtain ⟨p11_0, p11_1, p11_2, p11_3⟩ := h11c
                    linarith only [hlam, p11_0]
                · rcases h1bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [hlam, p37_0]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p37_1, u1elo0, u2ehi1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h4, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p37_1, u1elo0, u2ehi1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p37_1, u1elo0, u2ehi1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p37_1, u1elo0, u2ehi1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h0, hlam, p37_0]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [hlam, p37_0]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h4, hlam, p37_0]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h6, hlam, p37_1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h8, hlam, p37_1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h1, hlam, p37_0]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p37_1, u1elo2, u2ehi1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [hlam, p37_0]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h1, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p37_1, u1elo0, u2ehi1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h1, h10, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p37_1, u1elo0, u2ehi1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h2, hlam, p37_0]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p37_1, u1elo3, u2ehi1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h10, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p37_1, u1elo0]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [hlam, p37_0]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h10, hlam, p37_1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h3, hlam, p37_0]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h3, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p37_1, u1elo0, u2ehi1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p37_1, u1elo0, u2ehi1]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37_1, u1elo0]
                  · obtain ⟨p37_0, p37_1, p37_2, p37_3⟩ := h37c
                    linarith only [hlam, p37_0]
        · linarith only [h0, h3, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4, u2ehi1]
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi1]
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h66 | h66
    · rcases m.htr 0 1 4 (by decide) (by decide) with h67 | h67
      · rcases m.htr 0 1 5 (by decide) (by decide) with h68 | h68
        · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
          · linarith only [h0, h66, h69, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
          · linarith only [h0, h66, h69, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
          · linarith only [h0, h66, h72, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
          · linarith only [h0, h66, h72, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h75 | h75
        · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
          · linarith only [h0, h66, h76, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
          · linarith only [h0, h66, h76, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
          · linarith only [h0, h66, h79, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
          · linarith only [h0, h66, h79, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h82 | h82
      · rcases m.htr 0 1 5 (by decide) (by decide) with h83 | h83
        · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
          · rcases m.htr 1 2 4 (by decide) (by decide) with h85 | h85
            · linarith only [h66, h82, h84, h85, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi3]
            · linarith only [h84, h85, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
            · linarith only [h84, h88, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h82, h88, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
          · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
            · linarith only [h66, h82, h91, h92, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi3]
            · linarith only [h91, h92, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
            · linarith only [h91, h95, hc23, hlam, hphi, u2ehi3]
            · linarith only [h82, h83, h95, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h98 | h98
        · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
          · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
            · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
              · linarith only [h101, h66, h98, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi4]
              · linarith only [h100, h101, hc25, hlam, hphi, u2ehi3]
            · linarith only [h100, h99, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h105 | h105
            · linarith only [h105, h99, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
              · linarith only [h107, h99, hc23, hlam, hphi, u2ehi4]
              · linarith only [h0, h107, h98, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
          · rcases m.htr 1 2 4 (by decide) (by decide) with h111 | h111
            · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
              · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                · rcases h1bigk with h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [hlam, p114_0]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h0, hlam, p114_0]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h66, hlam, p114_0]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h82, hlam, p114_0]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h98, hlam, p114_0]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [hc01, hlam, hphi, p114_1, u1elo1]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [hlam, p114_0]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h66, hc01, hlam, hphi, p114_1, u1elo1]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h113, hc45, hlam, hphi, ht01, ht0b, ht5b, p114_1, u1elo1]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h98, hc01, hlam, hphi, p114_1, u1elo1]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [hc01, hlam, hphi, p114_1, u1elo2]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h110, hlam, p114_1]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [hlam, p114_0]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h110, h113, h98, hc01, hlam, hphi, p114_1, u1elo1]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h110, h98, hc01, hlam, hphi, p114_1, u1elo1]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [hc01, hlam, hphi, p114_1, u1elo3]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h111, hlam, p114_0]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h111, h66, hc01, hlam, hphi, p114_1, u1elo1]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [hlam, p114_0]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h111, h98, hc01, hlam, hphi, p114_1, u1elo1]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [hc01, hlam, hphi, p114_1, u1elo4]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h112, hlam, p114_0]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h111, h113, h66, hc01, hlam, hphi, p114_1, u1elo1]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [h113, hlam, p114_0]
                  · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                    linarith only [hlam, p114_0]
                · rcases h1bigk with h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [hlam, p140_0]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h0, hlam, p140_0]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h66, hlam, p140_0]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h82, hlam, p140_0]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h98, hlam, p140_0]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [hc01, hlam, hphi, p140_1, u1elo1]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [hlam, p140_0]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h66, hc01, hlam, hphi, p140_1, u1elo1]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h82, hc01, hlam, hphi, p140_1, u1elo1]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h98, hc01, hlam, hphi, p140_1, u1elo1]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [hc01, hlam, hphi, p140_1, u1elo2]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h110, hlam, p140_1]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [hlam, p140_0]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h110, h82, hc01, hlam, hphi, p140_1, u1elo1]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h110, h113, h82, hc01, hlam, hphi, p140_1, u1elo1]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [hc01, hlam, hphi, p140_1, u1elo3]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h111, hlam, p140_0]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h113, h66, hc03, hc45, hlam, hphi, ht34, p140_1]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [hlam, p140_0]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h113, hlam, p140_1]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h112, hc01, hlam, hphi, p140_1, u1elo1]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h112, hlam, p140_0]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h112, h66, hc01, hlam, hphi, p140_1, u1elo1]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [h112, h82, hc01, hlam, hphi, p140_1, u1elo1]
                  · obtain ⟨p140_0, p140_1, p140_2, p140_3⟩ := h140c
                    linarith only [hlam, p140_0]
              · linarith only [h110, h112, hc25, hlam, hphi, u2ehi2]
            · linarith only [h110, h111, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h168 | h168
            · linarith only [h110, h168, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
              · linarith only [h110, h170, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h172 | h172
                · rcases h1bigk with h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c | h173c
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [hlam, p173_0]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h0, hlam, p173_0]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h66, hlam, p173_0]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h82, hlam, p173_0]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h98, hlam, p173_0]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h110, hc01, hc23, hlam, hphi, ht12, p173_1]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [hlam, p173_0]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h110, hlam, p173_0]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h168, hlam, p173_1]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h170, hlam, p173_1]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [hc01, hlam, hphi, p173_1, u1elo2]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p173_1, u1elo2, u2ehi1]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [hlam, p173_0]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h172, hc45, hlam, hphi, ht01, ht0b, ht5b, p173_1, u1elo2]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h0, h170, hc01, hlam, hphi, p173_1, u1elo2]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [hc01, hlam, hphi, p173_1, u1elo3]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h0, hc01, hlam, hphi, p173_1, u1elo3]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h66, hc01, hlam, hphi, p173_1, u1elo3]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [hlam, p173_0]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h0, h170, hc01, hlam, hphi, p173_1, u1elo3]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [hc01, hlam, hphi, p173_1, u1elo4]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h0, hc01, hlam, hphi, p173_1, u1elo4]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h0, h110, h172, hc01, hlam, hphi, p173_1, u1elo3]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [h172, hlam, p173_0]
                  · obtain ⟨p173_0, p173_1, p173_2, p173_3⟩ := h173c
                    linarith only [hlam, p173_0]
                · rcases h1bigk with h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [hlam, p199_0]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h0, hlam, p199_0]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h66, hlam, p199_0]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h82, hlam, p199_0]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h98, hlam, p199_0]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [hc01, hlam, hphi, p199_1, u1elo1]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [hlam, p199_0]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h110, hlam, p199_0]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h168, hlam, p199_1]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h170, hlam, p199_1]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [hc01, hlam, hphi, p199_1, u1elo2]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p199_1, u1elo2, u2ehi1]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [hlam, p199_0]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h82, hc01, hlam, hphi, p199_1, u1elo2]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h98, hc01, hlam, hphi, p199_1, u1elo2]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [hc01, hlam, hphi, p199_1, u1elo3]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h0, hc01, hlam, hphi, p199_1, u1elo3]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h172, hc13, hc45, hlam, hphi, ht34, p199_1]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [hlam, p199_0]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h172, hlam, p199_1]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [hc01, hlam, hphi, p199_1, u1elo4]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h0, hc01, hlam, hphi, p199_1, u1elo4]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h0, h110, hc01, hlam, hphi, p199_1, u1elo4]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [h82, hc01, hlam, hphi, p199_1, u1elo4]
                  · obtain ⟨p199_0, p199_1, p199_2, p199_3⟩ := h199c
                    linarith only [hlam, p199_0]

theorem n7l_sAA2_M_LI_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi8 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi8, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo3]

theorem n7l_sAA2_M_LI_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_M_LI_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_M_LR_H_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p0_1, u2elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h12 | h12
    · linarith only [h12, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h12, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h16 | h16
    · linarith only [h16, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h16, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h19 | h19
    · linarith only [h19, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h19, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h26 | h26
    · linarith only [h26, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h26, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h30 | h30
    · linarith only [h30, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h30, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h34 | h34
    · linarith only [h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h34, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_LR_H_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h18 | h18
    · linarith only [h18, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h18, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h22 | h22
    · linarith only [h22, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h22, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h25 | h25
    · linarith only [h25, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h25, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h29 | h29
    · linarith only [h29, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h29, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h36 | h36
    · linarith only [h36, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h36, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h43 | h43
    · linarith only [h43, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h43, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h46 | h46
    · linarith only [h46, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h46, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_LR_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · linarith only [h20, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h20, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h28 | h28
    · linarith only [h28, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h28, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_LR_H_L_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi5, u1elo0]

theorem n7l_sAA2_M_LR_H_L_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi5, u1elo0]

theorem n7l_sAA2_M_LR_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi5, u1elo0]

theorem n7l_sAA2_M_LR_H_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  linarith only [hlam, hphi, ht12, u1ehi1, u2elo1]

theorem n7l_sAA2_M_LR_H_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_M_LR_H_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc15 := m.hcor 1 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi4]
  · linarith only [h0, hc15, hlam, hphi, u1ehi0]

theorem n7l_sAA2_M_LR_M_IR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
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
  have h1ehi := hb1.2.1
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h4, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h4, h6, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h11, h4, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                  · linarith only [h15, h6, hlam, hphi, ht12, u1ehi2, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h17, h5, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h1, h14, h15, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                  · linarith only [h20, h6, hlam, hphi, ht12, u1ehi2, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h14, h22, h6, hlam, hphi, ht12, u1ehi2, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                      · linarith only [h14, h24, h6, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                      · linarith only [h24, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
            · linarith only [h5, hlam, hphi, ht12, u1ehi1, u2elo3]
          · linarith only [h4, hlam, hphi, ht12, u1ehi1, u2elo2]
        · linarith only [h3, hlam, hphi, ht01, ht12, u0ehi6, u2elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem n7l_sAA2_M_LR_M_IR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc12, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u1ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u1ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAA2_M_LR_M_IR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1ehi := hb1.2.1
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h3, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h11, h3, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14 | h14
                · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h15, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h15, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h18, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                  · linarith only [h0, h18, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
            · linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h23 | h23
          · linarith only [h23, h3, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h25 | h25
            · linarith only [h25, h3, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h27 | h27
              · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
                · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
                  · linarith only [h29, h3, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                    · linarith only [h1, h25, h29, h31, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
                              · linarith only [h1, h33, h37, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h1, h33, h34, h37, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1, h33, h34, h36, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1, h3, h31, h33, h34, h35, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
                        · linarith only [h1, h27, h28, h34, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi3]
                      · linarith only [h1, h27, h29, h33, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                  · linarith only [h3, h44, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                    · linarith only [h1, h25, h44, h46, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                        · linarith only [h28, h49, hc14, hlam, hphi, ht01, u0ehi8]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
                            · linarith only [h1, h23, h28, h44, h51, h52, hc23, hlam, hphi, ht12, u0ehi6, u0elo0, u1ehi1]
                            · linarith only [h1, h23, h44, h52, hc45, hlam, hphi, ht12, ht23, ht34, u0ehi6, u0elo0, u1ehi1]
                          · linarith only [h1, h48, h51, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h1, h27, h44, h48, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h57 | h57
                · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                  · linarith only [h3, h58, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                    · linarith only [h1, h25, h58, h60, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                      · linarith only [h1, h27, h62, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                          · linarith only [h2, h27, h3, h58, h62, h65, hc23, hlam, hphi, ht12, u0ehi6, u0elo0, u1ehi1]
                          · linarith only [h2, h3, h58, h62, h65, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
                        · linarith only [h57, h58, h62, h64, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
                  · linarith only [h0, h3, h69, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                    · linarith only [h1, h25, h69, h71, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                      · linarith only [h1, h27, h3, h73, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                        · linarith only [h2, h27, h3, h57, h75, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                          · linarith only [h27, h3, h77, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                          · linarith only [h2, h3, h69, h73, h77, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h82 | h82
    · linarith only [h0, h82, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h84 | h84
      · linarith only [h0, h84, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h86 | h86
        · rcases m.htr 0 2 4 (by decide) (by decide) with h87 | h87
          · rcases m.htr 0 2 5 (by decide) (by decide) with h88 | h88
            · rcases m.htr 0 3 4 (by decide) (by decide) with h89 | h89
              · rcases m.htr 0 4 5 (by decide) (by decide) with h90 | h90
                · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h92 | h92
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h97 | h97
                              · linarith only [h86, h95, h97, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h86, h95, h96, h97, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h86, h89, h90, h96, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
                          · linarith only [h86, h89, h95, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                        · linarith only [h84, h86, h89, h90, h94, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                      · linarith only [h86, h89, h93, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi2]
                    · linarith only [h82, h91, h92, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h91, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h109 | h109
                        · linarith only [h106, h108, h109, h90, hc12, hlam, hphi, ht01, u0ehi8]
                        · linarith only [h109, h84, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                      · linarith only [h108, h86, h89, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi2]
                    · linarith only [h107, h88, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                  · linarith only [h0, h106, h86, hlam, hphi, u0ehi5, u0elo1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h115 | h115
                · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                      · linarith only [h116, h118, h82, h89, hc12, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h118, h82, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h117, h88, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
                  · linarith only [h0, h116, h86, hlam, hphi, u0ehi5, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h125 | h125
                      · linarith only [h123, h125, h82, h89, hc12, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h125, h82, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h115, h124, h82, h88, h89, hc45, hlam, hphi, ht23, ht34, u0ehi5, u0elo1, u2ehi1]
                  · linarith only [h0, h123, h86, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h86, h88, hc25, hlam, hphi, u2ehi2]
          · linarith only [h86, h87, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h132 | h132
          · linarith only [h132, h86, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h134 | h134
            · linarith only [h134, h86, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h136 | h136
              · rcases m.htr 0 4 5 (by decide) (by decide) with h137 | h137
                · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
                  · linarith only [h138, h86, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h138, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h141 | h141
                  · linarith only [h141, h86, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h141, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h144 | h144
                · rcases m.htr 1 2 3 (by decide) (by decide) with h145 | h145
                  · linarith only [h0, h145, h86, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h145, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
                  · linarith only [h0, h148, h86, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h148, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem n7l_sAA2_M_LR_M_LI_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h2elo := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases h1bigk with h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [hlam, p7_0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7_1, u1elo0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  rcases p7_3 (m.d 0 1) (by simp) with h10 | h10
                  · rcases p7_3 (m.d 1 2) (by simp) with h11 | h11
                    · linarith only [h0, h11, hlam]
                    · linarith only [h11, h4, hlam]
                  · linarith only [h10, hlam, p7_0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  rcases p7_3 (m.d 0 1) (by simp) with h15 | h15
                  · rcases p7_3 (m.d 1 2) (by simp) with h16 | h16
                    · linarith only [h0, h16, hlam]
                    · linarith only [h16, h5, hlam]
                  · linarith only [h15, hlam, p7_0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  rcases p7_3 (m.d 0 1) (by simp) with h20 | h20
                  · rcases p7_3 (m.d 1 2) (by simp) with h21 | h21
                    · linarith only [h0, h21, hlam]
                    · linarith only [h21, h6, hlam]
                  · linarith only [h20, hlam, p7_0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h0, hlam, p7_0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [hlam, p7_0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7_1, u1elo0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7_1, u1elo0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p7_1, u1elo0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [hc01, hlam, hphi, p7_1, u1elo2]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h4, hlam, p7_1]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [hlam, p7_0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h0, h4, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, p7_1, u0elo0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h0, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, p7_1, u1elo0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h1, hlam, p7_0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h5, hlam, p7_0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7_1, u1elo0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [hlam, p7_0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h0, h5, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, p7_1, u1elo0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h2, hlam, p7_0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h6, hlam, p7_0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7_1, u1elo0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [h0, h6, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7_1, u1elo0]
                · obtain ⟨p7_0, p7_1, p7_2, p7_3⟩ := h7c
                  linarith only [hlam, p7_0]
              · rcases h1bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [hlam, p45_0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45_1, u1elo0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  rcases p45_3 (m.d 0 1) (by simp) with h48 | h48
                  · rcases p45_3 (m.d 1 2) (by simp) with h49 | h49
                    · linarith only [h0, h49, hlam]
                    · linarith only [h4, h49, hlam]
                  · linarith only [h48, hlam, p45_0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  rcases p45_3 (m.d 0 1) (by simp) with h53 | h53
                  · rcases p45_3 (m.d 1 2) (by simp) with h54 | h54
                    · linarith only [h0, h54, hlam]
                    · linarith only [h5, h54, hlam]
                  · linarith only [h53, hlam, p45_0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h4, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45_1, u1elo0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h0, hlam, p45_0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [hlam, p45_0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45_1, u1elo0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h2, h5, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p45_1, u1elo0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h6, hlam, p45_1]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [hc01, hlam, hphi, p45_1, u1elo2]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h4, hlam, p45_1]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [hlam, p45_0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h2, h4, h5, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p45_1, u1elo0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h4, h6, hlam, p45_1]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h1, hlam, p45_0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h5, hlam, p45_0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45_1, u1elo0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [hlam, p45_0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h5, h6, hlam, p45_1]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h2, hlam, p45_0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p45_1, u1elo0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p45_1, u1elo0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p45_1, u1elo0]
                · obtain ⟨p45_0, p45_1, p45_2, p45_3⟩ := h45c
                  linarith only [hlam, p45_0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
              · rcases h1bigk with h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [hlam, p80_0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p80_1, u1elo0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  rcases p80_3 (m.d 0 1) (by simp) with h83 | h83
                  · rcases p80_3 (m.d 1 2) (by simp) with h84 | h84
                    · linarith only [h0, h84, hlam]
                    · linarith only [h4, h84, hlam]
                  · linarith only [h83, hlam, p80_0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h4, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p80_1, u1elo0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  rcases p80_3 (m.d 0 1) (by simp) with h89 | h89
                  · rcases p80_3 (m.d 1 2) (by simp) with h90 | h90
                    · linarith only [h0, h90, hlam]
                    · linarith only [h79, h90, hlam]
                  · linarith only [h89, hlam, p80_0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h0, hlam, p80_0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [hlam, p80_0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p80_1, u2elo3]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h5, hlam, p80_1]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p80_1, u2elo3]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [hc01, hlam, hphi, p80_1, u1elo2]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h4, hlam, p80_1]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [hlam, p80_0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h4, h5, hlam, p80_1]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h4, h5, h79, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p80_1, u2elo3]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h1, hlam, p80_0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p80_1, u0elo0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p80_1, u1elo0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [hlam, p80_0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h1, h79, hc25, hlam, hphi, ht01, ht0b, ht5b, p80_1, u1elo0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h2, hlam, p80_0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h79, hlam, p80_0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p80_1, u1elo0]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [h5, h79, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p80_1, u2elo3]
                · obtain ⟨p80_0, p80_1, p80_2, p80_3⟩ := h80c
                  linarith only [hlam, p80_0]
              · rcases h1bigk with h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [hlam, p114_0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p114_1, u1elo0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  rcases p114_3 (m.d 0 1) (by simp) with h117 | h117
                  · rcases p114_3 (m.d 1 2) (by simp) with h118 | h118
                    · linarith only [h0, h118, hlam]
                    · linarith only [h118, h4, hlam]
                  · linarith only [h117, hlam, p114_0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h4, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p114_1, u1elo0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h4, h79, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p114_1, u1elo0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h0, hlam, p114_0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [hlam, p114_0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h4, h79, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p114_1, u2elo4]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h5, hlam, p114_1]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h79, hlam, p114_1]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [hc01, hlam, hphi, p114_1, u1elo2]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h4, hlam, p114_1]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [hlam, p114_0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h4, h5, hlam, p114_1]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h4, h79, hlam, p114_1]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h1, hlam, p114_0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1, u0elo0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p114_1, u1elo0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [hlam, p114_0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h1, h4, h79, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p114_1, u1elo0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h2, hlam, p114_0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p114_1, u1elo4]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p114_1, u1elo0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p114_1, u1elo0]
                · obtain ⟨p114_0, p114_1, p114_2, p114_3⟩ := h114c
                  linarith only [hlam, p114_0]
          · linarith only [h3, h4, hc12, hlam, hphi, u2elo0]
        · linarith only [h3, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
      · linarith only [h2, hlam, hphi, ht01, u0ehi5, u1elo4]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi6, u1elo3]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem n7l_sAA2_M_LR_M_LI_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h2bigk := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h6, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                      · linarith only [h0, h11, h7, h9, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                        · linarith only [h0, h13, h7, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases h2bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h0, h13, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15_1, u1elo0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            rcases p15_3 (m.d 0 2) (by simp) with h18 | h18
                            · rcases p15_3 (m.d 1 2) (by simp) with h19 | h19
                              · linarith only [h0, h19, hlam]
                              · linarith only [h19, h6, hlam]
                            · linarith only [h18, hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            rcases p15_3 (m.d 0 2) (by simp) with h23 | h23
                            · rcases p15_3 (m.d 1 2) (by simp) with h24 | h24
                              · linarith only [h0, h24, hlam]
                              · linarith only [h24, h7, hlam]
                            · linarith only [h23, hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            rcases p15_3 (m.d 0 2) (by simp) with h28 | h28
                            · rcases p15_3 (m.d 1 2) (by simp) with h29 | h29
                              · linarith only [h0, h29, hlam]
                              · linarith only [h29, h8, hlam]
                            · linarith only [h28, hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h0, hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h0, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15_1, u1elo0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h0, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15_1, u1elo0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h0, h13, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15_1, u1elo0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h3, hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h6, hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h9, hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h11, hlam, p15_1]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h4, hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h7, hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h13, hc23, hc45, hlam, hphi, ht34, p15_1]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h13, hlam, p15_1]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h5, hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h8, hlam, p15_0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h0, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15_1, u1elo0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [h0, h8, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15_1, u1elo0]
                          · obtain ⟨p15_0, p15_1, p15_2, p15_3⟩ := h15c
                            linarith only [hlam, p15_0]
                  · linarith only [h0, h5, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h0, h4, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h3, h55, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h57 | h57
                  · linarith only [h0, h3, h57, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                        · rcases h2bigk with h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            rcases p62_3 (m.d 0 2) (by simp) with h64 | h64
                            · rcases p62_3 (m.d 1 2) (by simp) with h65 | h65
                              · linarith only [h0, h65, hlam]
                              · rcases p62_3 (m.d 2 3) (by simp) with h67 | h67
                                · linarith only [h3, h67, hlam]
                                · linarith only [h6, h67, hlam]
                            · linarith only [h0, h64, hlam]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h0, h57, h59, h61, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p62_1, u1elo0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h0, h57, h61, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p62_1, u1elo0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h0, h57, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p62_1, u1elo0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h0, hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h6, hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h55, hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h57, hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h3, hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p62_1, u1elo0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h0, h3, h57, h61, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p62_1, u1elo0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h0, h3, h57, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p62_1, u1elo0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h4, hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h0, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p62_1, u1elo0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h59, hlam, p62_1]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h0, h3, h57, h59, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p62_1, u1elo0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h5, hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h0, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p62_1, u1elo0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h60, hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [h61, hlam, p62_0]
                          · obtain ⟨p62_0, p62_1, p62_2, p62_3⟩ := h62c
                            linarith only [hlam, p62_0]
                        · rcases h2bigk with h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [hlam, p94_0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            rcases p94_3 (m.d 0 2) (by simp) with h96 | h96
                            · rcases p94_3 (m.d 1 2) (by simp) with h97 | h97
                              · linarith only [h0, h97, hlam]
                              · rcases p94_3 (m.d 2 3) (by simp) with h99 | h99
                                · linarith only [h3, h99, hlam]
                                · linarith only [h6, h99, hlam]
                            · linarith only [h0, h96, hlam]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h0, h59, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p94_1, u1elo0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h0, h55, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p94_1, u1elo0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h0, h57, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p94_1, u1elo0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h0, hlam, p94_0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [hlam, p94_0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h6, hlam, p94_0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h55, hlam, p94_0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h57, hlam, p94_0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h3, hlam, p94_0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p94_1, u1elo0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [hlam, p94_0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h0, h3, h55, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p94_1, u1elo0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h0, h3, h57, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p94_1, u1elo0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h4, hlam, p94_0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h61, hc12, hc45, hlam, hphi, ht23, ht34, p94_1]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h59, hlam, p94_1]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [hlam, p94_0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h61, hlam, p94_1]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h5, hlam, p94_0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h0, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p94_1, u1elo0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h60, hlam, p94_0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [h0, h3, h60, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p94_1, u1elo0]
                          · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                            linarith only [hlam, p94_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                        · linarith only [h126, h59, h60, hlam]
                        · rcases h2bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [hlam, p128_0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            rcases p128_3 (m.d 0 2) (by simp) with h130 | h130
                            · rcases p128_3 (m.d 1 2) (by simp) with h131 | h131
                              · linarith only [h0, h131, hlam]
                              · rcases p128_3 (m.d 2 3) (by simp) with h133 | h133
                                · linarith only [h133, h3, hlam]
                                · linarith only [h133, h6, hlam]
                            · linarith only [h0, h130, hlam]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h0, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p128_1, u1elo0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h0, h55, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p128_1, u1elo0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h0, h6, h60, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p128_1, u1elo0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h0, hlam, p128_0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [hlam, p128_0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h6, hlam, p128_0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h55, hlam, p128_0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h57, hlam, p128_0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h3, hlam, p128_0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h60, hc12, hc35, hlam, hphi, ht23, p128_1]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [hlam, p128_0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h0, h5, h55, h60, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p128_1, u1elo0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h60, hlam, p128_1]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h4, hlam, p128_0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h126, hc12, hc45, hlam, hphi, ht23, ht34, p128_1]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h59, hlam, p128_1]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [hlam, p128_0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h126, hlam, p128_1]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h5, hlam, p128_0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h0, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p128_1, u1elo0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h0, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p128_1, u1elo0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [h0, h5, h55, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p128_1, u1elo0]
                          · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                            linarith only [hlam, p128_0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h161 | h161
                        · rcases h2bigk with h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            rcases p162_3 (m.d 0 2) (by simp) with h164 | h164
                            · rcases p162_3 (m.d 1 2) (by simp) with h165 | h165
                              · linarith only [h0, h165, hlam]
                              · rcases p162_3 (m.d 2 3) (by simp) with h167 | h167
                                · linarith only [h167, h3, hlam]
                                · linarith only [h167, h6, hlam]
                            · linarith only [h0, h164, hlam]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h0, h160, hc35, hlam, hphi, ht01, ht0b, ht5b, p162_1, u1elo0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h0, h160, h59, hc35, hlam, hphi, ht01, ht0b, ht5b, p162_1, u1elo0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h0, h57, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p162_1, u1elo0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h0, hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h6, hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h55, hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h57, hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h3, hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h59, hc12, hc34, hlam, hphi, ht23, p162_1]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h59, hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h0, h4, h57, h59, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p162_1, u1elo0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h4, hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h0, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p162_1, u1elo0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p162_1, u1elo0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h0, h4, h57, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p162_1, u1elo0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h5, hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h0, h160, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p162_1, u1elo0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h160, hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [h161, hlam, p162_0]
                          · obtain ⟨p162_0, p162_1, p162_2, p162_3⟩ := h162c
                            linarith only [hlam, p162_0]
                        · linarith only [h160, h161, h59, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h195 | h195
                        · rcases h2bigk with h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c | h196c
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            rcases p196_3 (m.d 0 2) (by simp) with h198 | h198
                            · rcases p196_3 (m.d 1 2) (by simp) with h199 | h199
                              · linarith only [h0, h199, hlam]
                              · rcases p196_3 (m.d 2 3) (by simp) with h201 | h201
                                · linarith only [h201, h3, hlam]
                                · linarith only [h201, h6, hlam]
                            · linarith only [h0, h198, hlam]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h0, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p196_1, u1elo0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h0, h195, hc45, hlam, hphi, ht01, ht0b, ht5b, p196_1, u1elo0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h0, h57, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p196_1, u1elo0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h0, hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h6, hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h55, hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h57, hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h3, hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h160, hc12, hc35, hlam, hphi, ht23, p196_1]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h59, hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h160, hlam, p196_1]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h4, hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h0, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p196_1, u1elo0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p196_1, u1elo0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h0, h160, h4, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p196_1, u1elo0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h5, hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h0, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p196_1, u1elo0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h0, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p196_1, u1elo0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [h195, hlam, p196_0]
                          · obtain ⟨p196_0, p196_1, p196_2, p196_3⟩ := h196c
                            linarith only [hlam, p196_0]
                        · rcases h2bigk with h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [hlam, p228_0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            rcases p228_3 (m.d 0 2) (by simp) with h230 | h230
                            · rcases p228_3 (m.d 1 2) (by simp) with h231 | h231
                              · linarith only [h0, h231, hlam]
                              · rcases p228_3 (m.d 2 3) (by simp) with h233 | h233
                                · linarith only [h233, h3, hlam]
                                · linarith only [h233, h6, hlam]
                            · linarith only [h0, h230, hlam]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h0, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p228_1, u1elo0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h0, h55, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p228_1, u1elo0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h0, h57, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p228_1, u1elo0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h0, hlam, p228_0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [hlam, p228_0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h6, hlam, p228_0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h55, hlam, p228_0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h57, hlam, p228_0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h3, hlam, p228_0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p228_1, u1elo0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [hlam, p228_0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h59, hlam, p228_0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h160, hlam, p228_1]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h4, hlam, p228_0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h195, hc12, hc45, hlam, hphi, ht23, ht34, p228_1]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p228_1, u1elo0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [hlam, p228_0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h195, hlam, p228_1]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h5, hlam, p228_0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h0, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p228_1, u1elo0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h0, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p228_1, u1elo0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [h0, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p228_1, u1elo0]
                          · obtain ⟨p228_0, p228_1, p228_2, p228_3⟩ := h228c
                            linarith only [hlam, p228_0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
              · rcases m.htr 1 2 4 (by decide) (by decide) with h261 | h261
                · rcases m.htr 1 2 5 (by decide) (by decide) with h262 | h262
                  · linarith only [h262, h5, hlam, hphi, ht01, u0ehi6, u1elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h264 | h264
                    · linarith only [h0, h260, h264, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h266 | h266
                      · linarith only [h0, h261, h264, h266, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h268 | h268
                        · linarith only [h0, h261, h268, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases h2bigk with h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [hlam, p270_0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h268, h5, hc12, hc45, hlam, hphi, ht23, ht34, p270_1]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h268, h5, hc23, hc45, hlam, hphi, ht34, p270_1]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h264, h268, h5, hc23, hc45, hlam, hphi, ht34, p270_1]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h5, hlam, p270_0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h0, hlam, p270_0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [hlam, p270_0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h0, h268, h4, h5, hc23, hc45, hlam, hphi, ht01, ht34, p270_1, u0ehi8, u1elo0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h0, h264, h268, h4, h5, hc23, hc45, hlam, hphi, ht01, ht34, p270_1, u0ehi8, u1elo0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h262, hlam, p270_0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h3, hlam, p270_0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h260, hlam, p270_0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [hlam, p270_0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h264, hlam, p270_0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h266, hlam, p270_1]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h4, hlam, p270_0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h261, hlam, p270_0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h268, h4, h5, hc23, hc45, hlam, hphi, ht34, p270_1]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [hlam, p270_0]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h268, hlam, p270_1]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h268, h4, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p270_1, u0ehi8]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [h261, h268, hc24, hc45, hlam, hphi, p270_1]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            rcases p270_3 (m.d 0 2) (by simp) with h293 | h293
                            · linarith only [h293, h5, hlam]
                            · linarith only [h293, h3, hlam]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            rcases p270_3 (m.d 0 2) (by simp) with h296 | h296
                            · linarith only [h296, h5, hlam]
                            · linarith only [h296, h4, hlam]
                          · obtain ⟨p270_0, p270_1, p270_2, p270_3⟩ := h270c
                            linarith only [hlam, p270_0]
                · linarith only [h261, h4, h5, hc12, hc25, hlam, hphi]
              · linarith only [h260, h3, h5, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h302 | h302
            · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
              · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                · linarith only [h0, h304, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h307 | h307
                    · linarith only [h2, h303, h304, h307, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                      · linarith only [h2, h303, h304, h309, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h311 | h311
                        · rcases h2bigk with h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h306, h309, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p312_1, u0elo1]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h307, h4, hc23, hc34, hlam, hphi, p312_1]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h4, hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h307, h309, h4, hc23, hc34, hlam, hphi, p312_1]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h0, hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h0, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p312_1, u1elo0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h304, hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h2, h304, h309, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p312_1, u1elo0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h3, hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h303, hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h307, hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h309, hlam, p312_1]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h307, hc34, hlam, hphi, ht01, ht12, ht23, p312_1, u0ehi6]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h303, h307, hc23, hc34, hlam, hphi, p312_1]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            rcases p312_3 (m.d 0 2) (by simp) with h330 | h330
                            · linarith only [h330, h4, hlam]
                            · linarith only [h3, h330, hlam]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            rcases p312_3 (m.d 0 2) (by simp) with h334 | h334
                            · linarith only [h334, h4, hlam]
                            · linarith only [h302, h334, hlam]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h302, hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h306, hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h2, h304, h306, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p312_1, u1elo0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [h311, hlam, p312_0]
                          · obtain ⟨p312_0, p312_1, p312_2, p312_3⟩ := h312c
                            linarith only [hlam, p312_0]
                        · linarith only [h302, h311, h4, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                  · linarith only [h302, h303, h306, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h3, h303, h4, hc12, hc24, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h345 | h345
              · rcases m.htr 1 2 4 (by decide) (by decide) with h346 | h346
                · linarith only [h0, h3, h346, h4, hlam, hphi, ht01, u0ehi7, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h348 | h348
                  · linarith only [h2, h3, h302, h346, h348, hlam, hphi, ht01, u0ehi7, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h350 | h350
                    · linarith only [h2, h345, h346, h350, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h352 | h352
                      · linarith only [h2, h345, h346, h352, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h354 | h354
                        · rcases h2bigk with h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c | h355c
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h302, h350, h354, hc12, hc34, hlam, hphi, ht23, p355_1]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h302, h350, h354, hc23, hc34, hlam, hphi, p355_1]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h4, hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h302, hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h0, hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h0, h3, h302, h350, h354, hc23, hc34, hlam, hphi, ht01, p355_1, u0ehi7, u1elo0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h346, hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h348, hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h3, hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h345, hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h350, hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h352, hlam, p355_1]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h3, h350, hc34, hlam, hphi, ht01, ht12, ht23, p355_1, u0ehi7]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h345, h350, hc23, hc34, hlam, hphi, p355_1]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            rcases p355_3 (m.d 0 2) (by simp) with h373 | h373
                            · linarith only [h373, h4, hlam]
                            · linarith only [h3, h373, hlam]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h3, h302, h350, hc34, hlam, hphi, ht01, ht12, ht23, p355_1, u0ehi7]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h3, hc25, hlam, hphi, ht01, ht12, p355_1, u0ehi7]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h345, h352, hc23, hc35, hlam, hphi, p355_1]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            rcases p355_3 (m.d 0 2) (by simp) with h380 | h380
                            · linarith only [h302, h380, hlam]
                            · linarith only [h3, h380, hlam]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [h354, hlam, p355_0]
                          · obtain ⟨p355_0, p355_1, p355_2, p355_3⟩ := h355c
                            linarith only [hlam, p355_0]
                        · linarith only [h3, h354, h4, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
              · linarith only [h3, h345, h4, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h387 | h387
          · rcases m.htr 0 2 5 (by decide) (by decide) with h388 | h388
            · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
              · linarith only [h3, h387, h389, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h391 | h391
                · rcases m.htr 1 2 5 (by decide) (by decide) with h392 | h392
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h393 | h393
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h394 | h394
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h395 | h395
                        · linarith only [h0, h391, h395, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases h2bigk with h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h3, hc12, hc23, hlam, hphi, p397_1]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h3, hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            rcases p397_3 (m.d 0 2) (by simp) with h401 | h401
                            · rcases p397_3 (m.d 1 2) (by simp) with h402 | h402
                              · linarith only [h0, h402, hlam]
                              · linarith only [h391, h402, hlam]
                            · linarith only [h401, hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            rcases p397_3 (m.d 0 2) (by simp) with h406 | h406
                            · rcases p397_3 (m.d 1 2) (by simp) with h407 | h407
                              · linarith only [h0, h407, hlam]
                              · linarith only [h392, h407, hlam]
                            · linarith only [h406, hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h0, hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h389, hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h0, h393, hc34, hlam, hphi, ht0b, ht45, ht5b, p397_1, u0elo0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h1, h389, h393, h395, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p397_1, u1elo0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [hc23, hlam, hphi, ht01, ht12, p397_1, u0ehi6]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            rcases p397_3 (m.d 0 2) (by simp) with h417 | h417
                            · linarith only [h3, h417, hlam]
                            · linarith only [h0, h417, hlam]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            rcases p397_3 (m.d 0 2) (by simp) with h421 | h421
                            · linarith only [h3, h421, hlam]
                            · linarith only [h387, h421, hlam]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            rcases p397_3 (m.d 0 2) (by simp) with h424 | h424
                            · linarith only [h3, h424, hlam]
                            · linarith only [h388, h424, hlam]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h387, hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h391, hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h393, hlam, p397_1]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h395, hlam, p397_1]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h388, hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h392, hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h394, hlam, p397_0]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [h388, h393, hc34, hlam, hphi, ht0b, ht45, ht5b, p397_1, u0elo1]
                          · obtain ⟨p397_0, p397_1, p397_2, p397_3⟩ := h397c
                            linarith only [hlam, p397_0]
                      · linarith only [h3, h387, h394, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                    · linarith only [h3, h387, h393, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                  · linarith only [h3, h388, h392, hc12, hc23, hlam, hphi]
                · linarith only [h3, h387, h391, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
              · linarith only [h3, h387, h441, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h443 | h443
                · rcases m.htr 1 2 5 (by decide) (by decide) with h444 | h444
                  · linarith only [h1, h387, h388, h441, h444, hlam, hphi, ht01, u0ehi8, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h447 | h447
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h448 | h448
                        · linarith only [h1, h441, h443, h448, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases h2bigk with h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [hlam, p450_0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h388, h448, hc12, hc45, hlam, hphi, ht23, ht34, p450_1]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h3, hlam, p450_0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h388, h448, hc24, hc45, hlam, hphi, p450_1]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h388, hlam, p450_0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h0, hlam, p450_0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [hlam, p450_0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h441, hlam, p450_0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h0, h387, h388, h448, hc24, hc45, hlam, hphi, ht01, p450_1, u0ehi8, u1elo0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h444, hlam, p450_0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h387, hc23, hlam, hphi, ht01, ht12, p450_1, u0ehi8]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            rcases p450_3 (m.d 0 2) (by simp) with h462 | h462
                            · linarith only [h3, h462, hlam]
                            · linarith only [h0, h462, hlam]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [hlam, p450_0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            rcases p450_3 (m.d 0 2) (by simp) with h466 | h466
                            · linarith only [h3, h466, hlam]
                            · linarith only [h387, h466, hlam]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h387, h388, hc23, hlam, hphi, ht01, ht12, p450_1, u0ehi8]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h387, hlam, p450_0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h443, hlam, p450_0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h446, hlam, p450_1]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [hlam, p450_0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h448, hlam, p450_1]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h387, h448, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p450_1, u0ehi8]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h443, h448, hc24, hc45, hlam, hphi, p450_1]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [h447, hlam, p450_0]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            rcases p450_3 (m.d 0 2) (by simp) with h478 | h478
                            · linarith only [h388, h478, hlam]
                            · linarith only [h387, h478, hlam]
                          · obtain ⟨p450_0, p450_1, p450_2, p450_3⟩ := h450c
                            linarith only [hlam, p450_0]
                      · linarith only [h3, h387, h447, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                    · linarith only [h3, h387, h446, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                · linarith only [h3, h387, h443, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h485 | h485
            · rcases m.htr 1 2 3 (by decide) (by decide) with h486 | h486
              · linarith only [h3, h485, h486, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h488 | h488
                · linarith only [h1, h387, h485, h486, h488, hlam, hphi, ht01, u0ehi9, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h490 | h490
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h491 | h491
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h492 | h492
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h493 | h493
                        · rcases h2bigk with h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c | h494c
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h387, h491, hc12, hc23, hlam, hphi, p494_1]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h3, hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h387, hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            rcases p494_3 (m.d 0 2) (by simp) with h499 | h499
                            · rcases p494_3 (m.d 1 2) (by simp) with h500 | h500
                              · linarith only [h0, h500, hlam]
                              · linarith only [h490, h500, hlam]
                            · linarith only [h499, hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h0, hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h486, hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h488, hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h0, h492, hc35, hlam, hphi, ht01, ht0b, ht5b, p494_1, u1elo0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [hc23, hlam, hphi, ht01, ht12, p494_1, u0ehi6]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            rcases p494_3 (m.d 0 2) (by simp) with h510 | h510
                            · linarith only [h3, h510, hlam]
                            · linarith only [h0, h510, hlam]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h387, h485, hc23, hlam, hphi, ht01, ht12, p494_1, u0ehi9]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            rcases p494_3 (m.d 0 2) (by simp) with h515 | h515
                            · linarith only [h3, h515, hlam]
                            · linarith only [h485, h515, hlam]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h485, hc24, hlam, hphi, ht01, ht12, p494_1, u0ehi9]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            rcases p494_3 (m.d 0 2) (by simp) with h519 | h519
                            · linarith only [h387, h519, hlam]
                            · linarith only [h0, h519, hlam]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h491, hlam, p494_1]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            rcases p494_3 (m.d 0 2) (by simp) with h524 | h524
                            · linarith only [h387, h524, hlam]
                            · linarith only [h485, h524, hlam]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h485, hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h490, hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h492, hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [h493, hlam, p494_0]
                          · obtain ⟨p494_0, p494_1, p494_2, p494_3⟩ := h494c
                            linarith only [hlam, p494_0]
                        · linarith only [h387, h485, h493, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                      · linarith only [h3, h485, h492, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · linarith only [h3, h485, h491, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                  · linarith only [h3, h485, h490, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h536 | h536
              · linarith only [h3, h536, hlam, hphi, ht01, u0ehi6, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h538 | h538
                · linarith only [h1, h387, h536, h538, hlam, hphi, ht01, u0ehi6, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h540 | h540
                  · linarith only [h1, h485, h536, h540, hlam, hphi, ht01, u0ehi6, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h542 | h542
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h543 | h543
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h544 | h544
                        · rcases h2bigk with h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h485, h542, h544, hc12, hc23, hlam, hphi, p545_1]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h3, hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h387, hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h485, hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h0, hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h536, hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h538, hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h540, hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [hc23, hlam, hphi, ht01, ht12, p545_1, u0ehi6]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            rcases p545_3 (m.d 0 2) (by simp) with h557 | h557
                            · linarith only [h3, h557, hlam]
                            · linarith only [h0, h557, hlam]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h387, hc23, hlam, hphi, ht01, ht12, p545_1, u0ehi6]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h485, hc23, hlam, hphi, ht01, ht12, p545_1, u0ehi6]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [hc24, hlam, hphi, ht01, ht12, p545_1, u0ehi6]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            rcases p545_3 (m.d 0 2) (by simp) with h564 | h564
                            · linarith only [h387, h564, hlam]
                            · linarith only [h0, h564, hlam]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h542, hlam, p545_1]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h485, h542, hc23, hlam, hphi, ht01, ht12, p545_1, u0ehi6]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [hc25, hlam, hphi, ht01, ht12, p545_1, u0ehi6]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            rcases p545_3 (m.d 0 2) (by simp) with h571 | h571
                            · linarith only [h485, h571, hlam]
                            · linarith only [h0, h571, hlam]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h543, hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [h544, hlam, p545_0]
                          · obtain ⟨p545_0, p545_1, p545_2, p545_3⟩ := h545c
                            linarith only [hlam, p545_0]
                        · linarith only [h387, h544, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                      · linarith only [h3, h543, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                    · linarith only [h3, h542, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
      · linarith only [h2, hlam, hphi, ht01, u0ehi5, u1elo3]
    · linarith only [h0, h1, hlam, hphi, ht01, u0ehi6, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem n7l_sAA2_M_LR_M_LI_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
          · linarith only [h1, h3, h5, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi3]
          · linarith only [h0, h2, h5, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
        · linarith only [h0, h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
          · linarith only [h1, h10, h2, h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h1, h12, h16, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h1, h12, h13, h16, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1, h12, h13, h15, h2, hlam, hphi, ht01, u0ehi6, u1elo0]
                · linarith only [h14, h8, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h10, h13, h21, h22, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h2, h22, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                · linarith only [h1, h12, h21, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
              · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                · linarith only [h12, h27, h8, hc23, hlam, hphi, u2ehi1]
                · linarith only [h27, h8, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                · linarith only [h12, h30, h8, hc23, hlam, hphi, u2ehi1]
                · linarith only [h30, h8, hc34, hlam, hphi, ht23, u2ehi1]
    · linarith only [h1, hlam, hphi, ht01, u0ehi5, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem n7l_sAA2_M_LR_M_LR_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi8 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi8, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo3]

theorem n7l_sAA2_M_LR_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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

theorem n7l_sAA2_M_LR_M_LR_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
