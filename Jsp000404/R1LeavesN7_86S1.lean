import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_23_L_R_L_0_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h0emin := hb0.2.2
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h1, h10, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · rcases h0emin with h12 | h12 | h12 | h12 | h12
                        · rcases h3bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hc13, hlam, hphi, p13_1, u3elo0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hc23, hlam, hphi, p13_1, u3elo0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            rcases p13_3 (m.d 0 3) (by simp) with h17 | h17
                            · rcases p13_3 (m.d 1 3) (by simp) with h18 | h18
                              · linarith only [h0, h18, hlam]
                              · linarith only [h18, h6, hlam]
                            · linarith only [h17, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            rcases p13_3 (m.d 0 3) (by simp) with h22 | h22
                            · rcases p13_3 (m.d 1 3) (by simp) with h23 | h23
                              · linarith only [h0, h23, hlam]
                              · linarith only [h23, h7, hlam]
                            · linarith only [h22, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h0, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h10, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p13_1, u3elo1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            rcases p13_3 (m.d 0 3) (by simp) with h30 | h30
                            · rcases p13_3 (m.d 1 3) (by simp) with h31 | h31
                              · rcases p13_3 (m.d 2 3) (by simp) with h32 | h32
                                · linarith only [h32, h4, hlam]
                                · linarith only [h32, h8, hlam]
                              · linarith only [h31, hlam, p13_0]
                            · linarith only [h2, h30, hlam]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            rcases p13_3 (m.d 0 3) (by simp) with h37 | h37
                            · rcases p13_3 (m.d 1 3) (by simp) with h38 | h38
                              · rcases p13_3 (m.d 2 3) (by simp) with h39 | h39
                                · linarith only [h39, h4, hlam]
                                · linarith only [h39, h9, hlam]
                              · linarith only [h38, hlam, p13_0]
                            · linarith only [h3, h37, hlam]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h1, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h4, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13_1, u2elo0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h1, h10, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13_1, u2elo0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h2, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h6, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h8, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h10, hlam, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h3, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h7, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h9, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p13_1, u3elo0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                        · linarith only [h12, hlam, ht01, ht12, u2elo0]
                        · linarith only [h12, hlam, ht01, ht12, ht23, u3elo0]
                        · linarith only [h12, h2, hlam, ht01, ht12, ht23, u3elo0]
                        · linarith only [h12, h3, hlam, ht01, ht12, ht23, u3elo0]
                    · linarith only [h0, h7, h9, hc23, hlam, hphi, u3elo0]
                  · linarith only [h2, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h3, h7, hc13, hlam, hphi, u3elo0]
              · linarith only [h2, h4, h6, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
              · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                · linarith only [h4, h5, h68, hlam]
                · linarith only [h3, h68, hc13, hlam, hphi, u3elo0]
              · linarith only [h2, h4, h67, hc23, hlam, hphi, u3elo0]
          · linarith only [h1, h4, hc12, hlam, hphi, u2elo0]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_10_12_23_L_R_L_I_H_R (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h1, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h4, hc34, hlam, hphi, u3ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
          · linarith only [h0, h1, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h7, hc34, hlam, hphi, u3ehi2]
      · linarith only [h1, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h11 | h11
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
        · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
            · linarith only [h0, h1, h12, h14, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
            · linarith only [h14, hc35, hlam, hphi, u3ehi2]
          · linarith only [h1, h11, h13, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
        · linarith only [h1, h11, h12, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
        · linarith only [h11, h19, hc12, hlam, hphi, ht01, u0ehi1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
          · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
            · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
              · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                · rcases h2bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h11, h23, hc12, hc24, hlam, hphi, p25_1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h1, hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h11, h23, hlam, p25_1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h11, hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h0, hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h21, h24, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p25_1, u3ehi4]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h0, h11, h23, hlam, p25_1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h19, hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hc23, hlam, hphi, ht01, ht12, p25_1, u0ehi1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    rcases p25_3 (m.d 0 2) (by simp) with h37 | h37
                    · linarith only [h1, h37, hlam]
                    · linarith only [h0, h37, hlam]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h11, h23, hc23, hlam, hphi, ht01, ht12, p25_1, u0ehi1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h11, hc23, hlam, hphi, ht01, ht12, p25_1, u0ehi1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hc24, hlam, hphi, ht01, ht12, p25_1, u0ehi1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    rcases p25_3 (m.d 0 2) (by simp) with h44 | h44
                    · linarith only [h11, h44, hc12, hc25, hlam, hphi, p25_1]
                    · linarith only [h0, h44, hlam]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h21, hlam, p25_1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h11, hc02, hc24, hlam, hphi, p25_1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hc25, hlam, hphi, ht01, ht12, p25_1, u0ehi1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    rcases p25_3 (m.d 0 2) (by simp) with h51 | h51
                    · linarith only [h11, h51, hlam]
                    · linarith only [h0, h51, hlam]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h22, hlam, p25_1]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [h23, hlam, p25_0]
                  · have p25_0 := h25c.1
                    have p25_1 := h25c.2.1
                    have p25_2 := h25c.2.2.1
                    have p25_3 := h25c.2.2.2
                    linarith only [hlam, p25_0]
                · linarith only [h24, hc45, hlam, hphi, ht34, u3ehi3]
              · linarith only [h21, h23, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h22, hc35, hlam, hphi, u3ehi2]
          · linarith only [h1, h21, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h61 | h61
    · rcases m.htr 0 2 5 (by decide) (by decide) with h62 | h62
      · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
        · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
          · linarith only [h61, h64, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h64, hc34, hlam, hphi, u3ehi2]
        · linarith only [h0, h63, hc25, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h61, h62, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h69 | h69
      · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
        · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
          · rcases m.htr 2 3 5 (by decide) (by decide) with h72 | h72
            · linarith only [h61, h69, h72, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
            · linarith only [h72, hc35, hlam, hphi, u3ehi2]
          · linarith only [h61, h69, h71, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
        · linarith only [h0, h69, h70, hc02, hlam, hphi, u0ehi0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h77 | h77
        · linarith only [h69, h77, hc12, hlam, hphi, ht01, u0ehi1]
        · linarith only [h0, h77, hc25, hlam, hphi, ht01, ht12, u0ehi0]

theorem r1l7_10_12_23_L_R_L_R_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h3, h5, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · rcases h3bigk with h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c | h9c
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [hc13, hlam, hphi, p9_1, u3elo0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [hc23, hlam, hphi, p9_1, u3elo0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    rcases p9_3 (m.d 0 3) (by simp) with h13 | h13
                    · rcases p9_3 (m.d 1 3) (by simp) with h14 | h14
                      · linarith only [h1, h14, hlam]
                      · linarith only [h14, h4, hlam]
                    · linarith only [h13, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    rcases p9_3 (m.d 0 3) (by simp) with h18 | h18
                    · rcases p9_3 (m.d 1 3) (by simp) with h19 | h19
                      · linarith only [h1, h19, hlam]
                      · linarith only [h19, h3, h6, hlam]
                    · linarith only [h18, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h1, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h5, hlam, hphi, ht23, p9_1, u2ehi3, u3elo1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    rcases p9_3 (m.d 0 3) (by simp) with h26 | h26
                    · rcases p9_3 (m.d 1 3) (by simp) with h27 | h27
                      · rcases p9_3 (m.d 2 3) (by simp) with h28 | h28
                        · linarith only [h28, h3, hlam]
                        · linarith only [h28, h5, hlam]
                      · linarith only [h27, hlam, p9_0]
                    · linarith only [h1, h26, hlam, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    rcases p9_3 (m.d 0 3) (by simp) with h33 | h33
                    · rcases p9_3 (m.d 1 3) (by simp) with h34 | h34
                      · rcases p9_3 (m.d 2 3) (by simp) with h35 | h35
                        · linarith only [h3, h35, hlam]
                        · linarith only [h35, h6, hlam]
                      · linarith only [h34, hlam, p9_0]
                    · linarith only [h1, h33, hlam, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h2, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h3, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h0, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [hc03, hlam, hphi, p9_1, u3elo3]
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
                    linarith only [h7, hlam, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h0, h3, h6, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h3, h6, hlam, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h6, hlam, p9_0]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [h0, h3, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9_1]
                  · have p9_0 := h9c.1
                    have p9_1 := h9c.2.1
                    have p9_2 := h9c.2.2.1
                    have p9_3 := h9c.2.2.2
                    linarith only [hlam, p9_0]
              · linarith only [h6, hlam, hphi, ht23, u2ehi2, u3elo4]
            · linarith only [h5, hlam, hphi, ht23, u2ehi2, u3elo3]
          · linarith only [h3, h4, hlam, hphi, ht23, u2ehi2, u3elo3]
        · linarith only [h3, hlam, hphi, ht23, u2ehi1, u3elo2]
      · linarith only [h2, hlam, hphi, ht23, u2ehi0, u3elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h61 | h61
    · rcases m.htr 0 2 3 (by decide) (by decide) with h62 | h62
      · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
        · rcases m.htr 1 3 4 (by decide) (by decide) with h64 | h64
          · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
            · rcases m.htr 2 3 5 (by decide) (by decide) with h66 | h66
              · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                · linarith only [h0, h61, h63, h65, h67, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                · rcases h3bigk with h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [hlam, p69_0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h63, h65, hlam, hphi, ht23, p69_1, u2ehi3, u3elo0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h65, hlam, hphi, ht23, p69_1, u2ehi3, u3elo0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    rcases p69_3 (m.d 0 3) (by simp) with h73 | h73
                    · rcases p69_3 (m.d 1 3) (by simp) with h74 | h74
                      · linarith only [h61, h74, hlam]
                      · linarith only [h64, h74, hlam]
                    · linarith only [h73, hlam, p69_0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    rcases p69_3 (m.d 0 3) (by simp) with h78 | h78
                    · rcases p69_3 (m.d 1 3) (by simp) with h79 | h79
                      · linarith only [h61, h79, hlam]
                      · linarith only [h63, h65, h79, hlam, hphi, ht23, p69_1, u2ehi3, u3elo0]
                    · linarith only [h78, hlam, p69_0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h61, hlam, p69_0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [hlam, p69_0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h0, h61, h65, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p69_1, u2ehi3]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h0, h61, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p69_1]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h0, h61, h67, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p69_1]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h62, hlam, p69_0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h63, hlam, p69_0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [hlam, p69_0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h0, h61, h63, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p69_1]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h0, h61, h63, h67, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p69_1]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [hlam, hphi, ht01, ht12, ht23, p69_1, u0ehi2, u3elo3]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h64, hlam, p69_0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h65, hlam, p69_0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [hlam, p69_0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h67, hlam, p69_1]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h0, h61, h63, h66, hc12, hlam, hphi, ht01, p69_1, u0ehi2]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h63, h66, hlam, p69_1]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h66, hlam, p69_0]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [h0, h61, h63, h66, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p69_1]
                  · have p69_0 := h69c.1
                    have p69_1 := h69c.2.1
                    have p69_2 := h69c.2.2.1
                    have p69_3 := h69c.2.2.2
                    linarith only [hlam, p69_0]
              · linarith only [h65, h66, hlam, hphi, ht23, u2ehi3, u3elo4]
            · linarith only [h65, hlam, hphi, ht23, u2ehi2, u3elo3]
          · linarith only [h63, h64, hlam, hphi, ht23, u2ehi2, u3elo3]
        · linarith only [h0, h63, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h61, h62, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo2]
    · linarith only [h61, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_10_13_25_L_R_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
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
                  linarith only [h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h3, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h5, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo4]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h4, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h6, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h4, hc04, hc25, hlam, hphi, ht0b, ht5b, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, h3, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7_1, u3elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
              · rcases h5bigk with h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c | h33c
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [hlam, p33_0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h3, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p33_1, u3elo0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h0, hlam, p33_0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [hlam, p33_0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p33_1]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h0, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h6, hlam, p33_1]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h2, hlam, p33_1]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p33_1]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [hlam, p33_0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h2, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h2, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h3, hlam, p33_0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h5, hlam, p33_0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo4]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [hlam, p33_0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h5, h6, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p33_1]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h4, hlam, p33_0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h4, hc04, hc15, hlam, hphi, ht0b, ht5b, p33_1]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h3, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [h3, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p33_1, u3elo0]
                · have p33_0 := h33c.1
                  have p33_1 := h33c.2.1
                  have p33_2 := h33c.2.2.1
                  have p33_3 := h33c.2.2.2
                  linarith only [hlam, p33_0]
            · linarith only [h3, h5, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h60 | h60
            · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
              · linarith only [h4, h61, hc14, hlam, hphi, ht01, u0ehi3]
              · rcases h5bigk with h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h3, h61, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p63_1, u3elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h4, hlam, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h0, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h61, hlam, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, hlam, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p63_1, u3elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h2, h3, h4, hlam, hphi, ht01, ht12, ht23, p63_1, u0ehi3, u3elo0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h3, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h60, hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h60, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h4, h60, hc15, hlam, hphi, ht01, p63_1, u0ehi3]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p63_1, u0ehi4]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [h61, hc14, hc45, hlam, hphi, p63_1]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  rcases p63_3 (m.d 0 5) (by simp) with h86 | h86
                  · linarith only [h4, h86, hlam]
                  · linarith only [h2, h86, hlam]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  rcases p63_3 (m.d 0 5) (by simp) with h89 | h89
                  · linarith only [h4, h89, hlam]
                  · linarith only [h3, h89, hlam]
                · have p63_0 := h63c.1
                  have p63_1 := h63c.2.1
                  have p63_2 := h63c.2.2.1
                  have p63_3 := h63c.2.2.2
                  linarith only [hlam, p63_0]
            · linarith only [h3, h60, hc13, hlam, hphi, u3elo0]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h95 | h95
        · linarith only [h1, h2, h95, hlam]
        · linarith only [h95, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h99 | h99
    · rcases m.htr 0 2 5 (by decide) (by decide) with h100 | h100
      · rcases m.htr 0 3 5 (by decide) (by decide) with h101 | h101
        · rcases m.htr 0 4 5 (by decide) (by decide) with h102 | h102
          · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
            · linarith only [h0, h103, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]
            · linarith only [h101, h103, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h106 | h106
            · linarith only [h0, h106, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]
            · linarith only [h101, h106, hc13, hlam, hphi, u3elo0]
        · linarith only [h101, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h110 | h110
        · linarith only [h100, h110, h99, hlam]
        · linarith only [h110, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
    · linarith only [h99, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]

theorem r1l7_11_12_14_25_L_0_L_0_L_0_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h3, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h6, hc13, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                · linarith only [h11, h12, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h0, h12, h14, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h11, h14, h5, hc23, hc34, hlam, hphi]
              · linarith only [h11, hc13, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h2, h4, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
          · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
              · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                    · linarith only [h19, h22, h24, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h24, hc34, hlam, hphi, ht45, u5elo4]
                  · linarith only [h21, h23, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h19, h22, h3, hc24, hlam, hphi, u4elo3]
              · linarith only [h21, hc13, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h19, h20, h3, hc24, hlam, hphi, u4elo3]
          · linarith only [h19, h2, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
        · linarith only [h0, h2, h32, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
          · linarith only [h0, h2, h34, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
            · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
              · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h40 | h40
                    · linarith only [h1, h36, h40, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h40, hc34, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1, h2, h37, h38, h39, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h32, h38, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h37, hc13, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h46 | h46
              · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                · linarith only [h36, h46, h47, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h32, h47, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h46, hc13, hlam, hphi, ht34, ht45, u5elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h51 | h51
      · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
        · linarith only [h0, h1, h52, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
        · linarith only [h0, h1, h52, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
        · linarith only [h0, h1, h55, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
        · linarith only [h0, h1, h55, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h58 | h58
    · rcases m.htr 0 2 4 (by decide) (by decide) with h59 | h59
      · rcases m.htr 1 2 3 (by decide) (by decide) with h60 | h60
        · rcases m.htr 1 2 4 (by decide) (by decide) with h61 | h61
          · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
            · linarith only [h0, h58, h62, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
              · linarith only [h0, h58, h64, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h64, hc13, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h0, h61, hc01, hlam, hphi, ht12, u2elo3]
        · linarith only [h0, h58, h60, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · linarith only [h0, h58, h59, hc13, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h70 | h70
      · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
        · rcases m.htr 1 2 4 (by decide) (by decide) with h72 | h72
          · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
            · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
              · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                · rcases m.htr 2 3 5 (by decide) (by decide) with h76 | h76
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                    · linarith only [h71, h75, h77, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h77, hc34, hlam, hphi, ht45, u5elo4]
                  · linarith only [h75, h76, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h81 | h81
                  · linarith only [h71, h73, h75, h81, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h81, hc23, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h74, hc13, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h58, h73, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · linarith only [h70, h72, hc12, hlam, hphi, u2elo0]
        · linarith only [h0, h71, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
        · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
          · linarith only [h70, h89, hc02, hlam, hphi, u2elo1]
          · linarith only [h88, h89, hc23, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h88, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_11_12_14_25_L_0_L_0_L_0_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · linarith only [h1, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
              · linarith only [h3, h4, h5, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
              · linarith only [h0, h7, hc24, hlam, hphi, u4elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
            · linarith only [h1, h10, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
              · linarith only [h12, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
              · linarith only [h0, h12, hc24, hlam, hphi, u4elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
          · linarith only [h1, h15, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
            · linarith only [h15, h17, h2, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
              · linarith only [h19, h2, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
              · linarith only [h0, h15, h19, hc23, hlam, hphi, ht34, u4elo0]
      · linarith only [h1, h2, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
      · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
        · linarith only [h1, h24, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
          · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
            · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
              · linarith only [h23, h24, h27, h28, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
              · linarith only [h0, h26, h28, hc34, hlam, hphi, u4elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
              · linarith only [h23, h31, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
              · linarith only [h0, h26, h31, hc34, hlam, hphi, u4elo0]
          · linarith only [h1, h26, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
        · linarith only [h1, h35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
          · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
            · rcases m.htr 2 4 5 (by decide) (by decide) with h39 | h39
              · rcases m.htr 3 4 5 (by decide) (by decide) with h40 | h40
                · linarith only [h37, h40, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                · linarith only [h0, h40, hc34, hlam, hphi, u4elo0]
              · linarith only [h0, h39, hc24, hlam, hphi, u4elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
              · linarith only [h37, h38, h44, hlam]
              · linarith only [h0, h44, hc24, hlam, hphi, u4elo0]
          · linarith only [h1, h37, hc12, hlam, hphi, ht23, ht34, u4elo3]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
    · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
      · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
        · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
          · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
            · linarith only [h48, h52, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
              · linarith only [h0, h49, h54, hc04, hlam, hphi, u4elo1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                · linarith only [h54, h56, hc24, hlam, hphi, u4elo3]
                · linarith only [h51, h52, h56, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
            · linarith only [h51, h59, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
              · linarith only [h0, h61, hc04, hlam, hphi, u4elo2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                · linarith only [h51, h61, h63, hc23, hlam, hphi, ht34, u4elo3]
                · linarith only [h51, h63, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
          · linarith only [h48, h50, h66, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
            · linarith only [h49, h50, h66, h68, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
              · linarith only [h49, h50, h70, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
              · linarith only [h49, h50, h66, h70, hc23, hlam, hphi, ht34, u4elo4]
      · linarith only [h48, h49, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
      · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
        · linarith only [h48, h75, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
          · rcases m.htr 2 3 5 (by decide) (by decide) with h78 | h78
            · rcases m.htr 2 4 5 (by decide) (by decide) with h79 | h79
              · linarith only [h74, h75, h78, h79, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
              · linarith only [h74, h75, h77, h79, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h82 | h82
              · linarith only [h74, h82, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
              · linarith only [h48, h74, h77, h78, h82, hc34, hlam, hphi, u4elo4]
          · linarith only [h48, h77, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
        · linarith only [h48, h86, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
          · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
            · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
              · linarith only [h0, h90, hc04, hlam, hphi, u4elo2]
              · linarith only [h74, h90, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h93 | h93
              · linarith only [h0, h93, hc04, hlam, hphi, u4elo2]
              · linarith only [h74, h93, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · linarith only [h48, h88, hc12, hlam, hphi, ht23, ht34, u4elo3]

theorem r1l7_11_12_14_25_L_0_L_0_L_R_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5emax := hb5.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
      · linarith only [h0, h1, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
      · linarith only [h1, h5, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
        · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
          · linarith only [h0, h1, h8, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
            · linarith only [h0, h1, h10, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi1]
            · rcases h5emax with h12 | h12 | h12 | h12 | h12
              · linarith only [h0, h1, h12, hlam, ht45, u4ehi1]
              · linarith only [h12, h5, hlam, ht45, u4ehi1]
              · linarith only [h12, h8, hlam, ht45, u4ehi2]
              · linarith only [h10, h12, hlam, ht45, u4ehi3]
              · linarith only [h0, h1, h12, hlam, ht45, u4ehi1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
          · linarith only [h0, h1, h18, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
            · rcases h5emax with h21 | h21 | h21 | h21 | h21
              · linarith only [h0, h1, h21, hlam, ht45, u4ehi1]
              · linarith only [h21, h5, hlam, ht45, u4ehi1]
              · linarith only [h18, h21, hlam, ht45, u4ehi2]
              · linarith only [h0, h1, h20, h21, hlam, ht45, u4ehi1]
              · linarith only [h0, h1, h21, hlam, ht45, u4ehi1]
            · rcases h5emax with h27 | h27 | h27 | h27 | h27
              · linarith only [h0, h1, h27, hlam, ht45, u4ehi1]
              · linarith only [h27, h5, hlam, ht45, u4ehi1]
              · linarith only [h18, h27, hlam, ht45, u4ehi2]
              · linarith only [h27, h7, hc23, hlam, ht34, ht45]
              · linarith only [h0, h1, h27, hlam, ht45, u4ehi1]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h33 | h33
    · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
      · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
        · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
          · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
            · rcases h5emax with h38 | h38 | h38 | h38 | h38
              · linarith only [h33, h38, hlam, ht45, u4ehi4]
              · linarith only [h34, h38, hlam, ht45, u4ehi4]
              · linarith only [h36, h38, hlam, ht45, u4ehi4]
              · linarith only [h37, h38, hlam, ht45, u4ehi4]
              · linarith only [h38, hlam, ht45, u4ehi4]
            · linarith only [h36, h37, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
          · linarith only [h0, h33, h36, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
          · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
            · rcases h5emax with h48 | h48 | h48 | h48 | h48
              · linarith only [h33, h48, hlam, ht45, u4ehi4]
              · linarith only [h34, h48, hlam, ht45, u4ehi4]
              · linarith only [h46, h48, hlam, ht45, u4ehi4]
              · linarith only [h35, h46, h48, hlam, ht45, u4ehi4]
              · linarith only [h48, hlam, ht45, u4ehi4]
            · linarith only [h0, h33, h47, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
          · linarith only [h0, h33, h46, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
      · linarith only [h0, h33, h34, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
      · linarith only [h33, h57, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
        · rcases m.htr 2 4 5 (by decide) (by decide) with h60 | h60
          · linarith only [h0, h57, h60, hc01, hlam, hphi, ht12, u2elo3]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
            · linarith only [h0, h57, h62, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases h5emax with h64 | h64 | h64 | h64 | h64
              · linarith only [h33, h64, hlam, ht45, u4ehi0]
              · linarith only [h0, h57, h64, hc01, hlam, ht12, ht23, ht34, ht45]
              · linarith only [h59, h62, h64, hlam, ht45, u4ehi3]
              · linarith only [h62, h64, hlam, ht45, u4ehi3]
              · linarith only [h0, h57, h64, hc01, hlam, ht12, ht23, ht34, ht45]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
          · linarith only [h0, h57, h70, hc01, hlam, hphi, ht12, u2elo3]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
            · linarith only [h0, h57, h72, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases h5emax with h74 | h74 | h74 | h74 | h74
              · linarith only [h33, h74, hlam, ht45, u4ehi0]
              · linarith only [h0, h57, h74, hc01, hlam, ht12, ht23, ht34, ht45]
              · linarith only [h70, h74, hlam, ht45, u4ehi2]
              · linarith only [h59, h74, hc23, hlam, ht34, ht45]
              · linarith only [h0, h57, h74, hc01, hlam, ht12, ht23, ht34, ht45]

theorem r1l7_11_12_14_25_L_R_L_0_L_0_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h10, h13, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · linarith only [h13, h9, hc34, hlam, hphi, u4elo1]
                          · linarith only [h12, h9, hc24, hlam, hphi, u4elo1]
                        · linarith only [h0, h10, h11, h5, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                        · linarith only [h0, h10, h18, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                            · rcases h5bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p22_1, u2elo0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p22_1, u2elo0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h18, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p22_1, u2elo0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22_1, u2elo0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h2, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h18, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, h18, h5, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p22_1, u2elo0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p22_1, u4elo1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h3, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h6, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h18, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22_1, u2elo4]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h4, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h8, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, h5, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p22_1, u2elo0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, h21, h5, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22_1, u2elo0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, h18, h21, h5, h7, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p22_1, u2elo0, u4elo4]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h9, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h20, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h21, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                            · linarith only [h10, h20, h21, hlam]
                          · linarith only [h20, h9, hc24, hlam, hphi, u4elo1]
                    · linarith only [h9, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
                  · linarith only [h3, h4, h8, hlam, hphi, ht12, u1ehi2, u2elo0]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
              · linarith only [h6, hlam, hphi, ht12, u1ehi1, u2elo4]
            · linarith only [h5, hlam, hphi, ht12, u1ehi1, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
            · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
              · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                  · linarith only [h1, h4, h58, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                    · linarith only [h57, h58, h60, hlam]
                    · linarith only [h60, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
                · linarith only [h57, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
              · linarith only [h56, hlam, hphi, ht12, u1ehi1, u2elo4]
            · linarith only [h55, hlam, hphi, ht12, u1ehi1, u2elo2]
        · linarith only [h0, h3, hlam, hphi, ht12, u1ehi1, u2elo4]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · linarith only [h0, hlam, hphi, ht12, u1ehi0, u2elo1]

theorem r1l7_11_12_14_25_L_R_L_0_L_R_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h1ehi := hb1.1
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
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
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h12, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                            · linarith only [h14, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                              · linarith only [h1, h10, h12, h16, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                              · linarith only [h16, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                        · linarith only [h11, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                          · linarith only [h10, h21, hlam, hphi, ht12, u1ehi2, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                            · linarith only [h23, h3, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                              · linarith only [h0, h25, h8, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                              · linarith only [h25, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                        · linarith only [h20, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
                    · linarith only [h9, hlam, hphi, ht12, u1ehi1, u2elo4]
                  · linarith only [h8, hlam, hphi, ht12, u1ehi1, u2elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                        · linarith only [h31, h34, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                          · linarith only [h3, h36, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                            · linarith only [h1, h3, h33, h36, h38, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
                              · linarith only [h34, h40, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
                                · linarith only [h1, h3, h33, h34, h42, hlam, hphi, ht12, u1ehi3, u2elo0]
                                · rcases h5bigk with h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [hlam, p44_0]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h3, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, p44_1, u2elo0, u5ehi1]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h3, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, p44_1, u2elo0, u5ehi2]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h3, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, p44_1, u2elo0, u5ehi3]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h7, hlam, p44_0]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h2, hlam, p44_0]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [hlam, p44_0]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p44_1, u5ehi2]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h2, h3, h38, h40, h6, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p44_1, u2elo0, u4ehi2]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h34, hlam, p44_0]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h5, hlam, p44_1]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h32, hlam, p44_1]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [hlam, p44_0]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h38, hlam, p44_1]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h40, hlam, p44_0]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h6, hlam, p44_1]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht12, ht23, p44_1, u1ehi4]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h3, h40, h6, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p44_1, u2elo0, u4ehi2]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [hlam, p44_0]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h42, hlam, p44_0]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h1, h2, h3, h33, h34, h36, hc23, hc45, hlam, hphi, ht12, ht34, p44_1, u1ehi3, u2elo0]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h1, h3, h33, h34, h36, hc23, hc45, hlam, hphi, ht12, ht34, p44_1, u1ehi3, u2elo0]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h40, hc45, hlam, hphi, p44_1, u4ehi2]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [h38, hc23, hc45, hlam, hphi, ht34, p44_1]
                                  · have p44_0 := h44c.1
                                    have p44_1 := h44c.2.1
                                    have p44_2 := h44c.2.2.1
                                    have p44_3 := h44c.2.2.2
                                    linarith only [hlam, p44_0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                        · linarith only [h0, h31, h4, h7, h70, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
                          · linarith only [h3, h72, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h74 | h74
                            · linarith only [h3, h74, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h76 | h76
                              · linarith only [h0, h31, h76, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                                · linarith only [h33, h70, h78, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                · linarith only [h3, h33, h6, h74, h78, hc23, hc45, hlam, hphi, ht12, ht34, u1ehi2, u2elo0]
                    · linarith only [h32, hlam, hphi, ht12, u1ehi1, u2elo4]
                  · linarith only [h31, hlam, hphi, ht12, u1ehi1, u2elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h83 | h83
                · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h87 | h87
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                          · linarith only [h3, h88, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                          · linarith only [h1, h6, h86, h88, hc23, hc35, hlam, hphi]
                        · linarith only [h4, h83, h87, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                          · linarith only [h86, h93, hlam, hphi, ht12, u1ehi2, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                            · linarith only [h1, h6, h93, h95, hlam, hphi, ht12, u1ehi2, u2elo3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h97 | h97
                              · linarith only [h84, h97, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                              · linarith only [h4, h83, h97, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                        · linarith only [h4, h83, h92, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi1]
                    · linarith only [h85, hlam, hphi, ht12, u1ehi1, u2elo4]
                  · linarith only [h84, hlam, hphi, ht12, u1ehi1, u2elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h105 | h105
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h106 | h106
                        · linarith only [h103, h106, h83, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h108 | h108
                          · linarith only [h108, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                          · linarith only [h1, h105, h108, h6, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                        · linarith only [h0, h103, h111, h4, h83, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                          · linarith only [h105, h113, hlam, hphi, ht12, u1ehi2, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                            · linarith only [h0, h103, h113, h115, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h117 | h117
                              · linarith only [h0, h103, h105, h111, h117, hlam, hphi, ht12, u1ehi2, u2elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h119 | h119
                                · linarith only [h105, h111, h119, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                · linarith only [h0, h104, h105, h117, h119, hc45, hlam, hphi, ht12, u1ehi2, u2elo0, u4ehi2]
                    · linarith only [h104, hlam, hphi, ht12, u1ehi1, u2elo4]
                  · linarith only [h103, hlam, hphi, ht12, u1ehi1, u2elo3]
            · linarith only [h4, h5, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
          · linarith only [h1, h3, h4, hlam, hphi, ht12, u1ehi2, u2elo3]
        · linarith only [h0, h3, hlam, hphi, ht12, u1ehi1, u2elo2]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · linarith only [h0, hlam, hphi, ht12, u1ehi0, u2elo1]

theorem r1l7_11_12_14_25_L_R_L_I_L_0_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
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
                        linarith only [hc15, hlam, hphi, p10_1, u5elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h7, h9, hc45, hlam, hphi, p10_1, u5elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h9, hc45, hlam, hphi, p10_1, u5elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hc45, hlam, hphi, p10_1, u5elo0]
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
                        linarith only [h7, h9, hc45, hlam, hphi, p10_1, u5elo1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, h9, hc45, hlam, hphi, p10_1, u5elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hc45, hlam, hphi, p10_1, u5elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hc25, hlam, hphi, ht12, p10_1, u1ehi4]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h3, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, h3, h9, hc45, hlam, hphi, p10_1, u5elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, h3, hc45, hlam, hphi, p10_1, u5elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hc35, hlam, hphi, ht12, ht23, p10_1, u1ehi4]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h5, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h7, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h7, hc45, hlam, hphi, p10_1, u5elo2]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hlam, hphi, ht12, ht23, ht34, p10_1, u1ehi4, u4elo4]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h6, hlam, p10_1]
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
                    · linarith only [h1, h6, h9, hc34, hlam, hphi, u4elo0]
                  · linarith only [h1, h6, h8, hc24, hlam, hphi, u4elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                    · rcases h5bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p40_1, u1ehi4, u5elo0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hc25, hlam, hphi, p40_1, u5elo0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h7, hc23, hlam, hphi, ht34, ht45, p40_1, u5elo0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hc45, hlam, hphi, p40_1, u5elo0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h2, hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h7, hc23, hlam, hphi, ht34, ht45, p40_1, u5elo1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h2, h7, hc23, hlam, hphi, ht34, ht45, p40_1, u5elo0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h2, hc45, hlam, hphi, p40_1, u5elo0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h2, hc25, hlam, hphi, ht12, p40_1, u1ehi4]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h3, hlam, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h7, hlam, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h2, h5, h7, hc45, hlam, hphi, p40_1, u5elo0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h2, h5, hlam, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h5, hlam, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h2, h5, hc25, hlam, hphi, p40_1, u5elo0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hlam, p40_0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h2, h5, hc45, hlam, hphi, p40_1, u5elo0]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h2, hlam, hphi, ht12, ht23, ht34, p40_1, u1ehi4, u4elo4]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h6, hlam, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h38, hlam, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [h39, hlam, p40_1]
                      · have p40_0 := h40c.1
                        have p40_1 := h40c.2.1
                        have p40_2 := h40c.2.2.1
                        have p40_3 := h40c.2.2.2
                        linarith only [hlam, p40_0]
                    · linarith only [h1, h39, h6, hc34, hlam, hphi, u4elo0]
                  · linarith only [h1, h38, h6, hc24, hlam, hphi, u4elo0]
              · linarith only [h6, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
            · linarith only [h5, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
          · linarith only [h4, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h74 | h74
    · linarith only [h0, h74, hc13, hlam, hphi, u1ehi3]
    · linarith only [h74, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

end R2N4
