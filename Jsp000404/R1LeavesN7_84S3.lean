import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_13_25_L_0_L_R_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h6, h9, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                  · linarith only [h4, h7, h8, h9, hc34, hlam, hphi, u3ehi4]
                · linarith only [h8, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · linarith only [h6, h7, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h14, h17, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi4]
                    · linarith only [h16, h17, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h14, h15, h16, h4, hc34, hlam, hphi, u3ehi4]
                · linarith only [h15, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
                · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
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
                            linarith only [h14, hc12, hlam, hphi, ht23, ht34, ht45, p27_1, u5elo0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [hlam, hphi, ht34, ht45, p27_1, u3ehi4, u5elo0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [hc45, hlam, hphi, p27_1, u5elo0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h1, hlam, p27_0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [hlam, p27_0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h14, hlam, p27_0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p27_1, u1elo4, u3ehi4]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h0, h14, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p27_1, u1elo0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h2, hlam, p27_1]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h0, h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p27_1, u1elo0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [hlam, p27_0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p27_1, u1elo0, u3ehi4]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h0, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p27_1, u1elo0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h3, hlam, p27_0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h22, hlam, p27_0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h24, hlam, p27_0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [hlam, p27_0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h22, hc45, hlam, hphi, p27_1, u5elo1]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [hc05, hlam, hphi, p27_1, u5elo4]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h22, h26, hc34, hlam, hphi, p27_1, u3ehi4]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h25, hlam, p27_0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [h26, hlam, p27_0]
                          · have p27_0 := h27c.1
                            have p27_1 := h27c.2.1
                            have p27_2 := h27c.2.2.1
                            have p27_3 := h27c.2.2.2
                            linarith only [hlam, p27_0]
                        · linarith only [h0, h2, h25, h26, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                      · linarith only [h25, h6, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h22, h24, h4, hlam, hphi, ht34, ht45, u3ehi1, u5elo1]
                  · linarith only [h22, h23, h4, hc34, hlam, hphi, u3ehi4]
                · linarith only [h22, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
        · linarith only [h3, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h59 | h59
        · rcases m.htr 1 2 3 (by decide) (by decide) with h60 | h60
          · linarith only [h0, h60, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
            · linarith only [h0, h2, h62, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
              · linarith only [h0, h2, h64, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h66 | h66
                · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h70 | h70
                        · rcases h5bigk with h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [hlam, p71_0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [hc15, hlam, hphi, p71_1, u5elo0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h2, hlam, p71_0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h2, hlam, hphi, ht34, ht45, p71_1, u3ehi4, u5elo2]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, p71_1, u5elo2]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h1, hlam, p71_0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [hlam, p71_0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h64, hlam, p71_0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p71_1, u1elo4, u3ehi4]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h1, hc45, hlam, hphi, ht01, ht0b, ht5b, p71_1, u1elo0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [hc05, hlam, hphi, p71_1, u5elo2]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [hc15, hlam, hphi, p71_1, u5elo2]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [hlam, p71_0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [hlam, hphi, ht34, ht45, p71_1, u3ehi4, u5elo2]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [hc45, hlam, hphi, p71_1, u5elo2]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h59, hlam, p71_0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h66, hlam, p71_0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h68, hlam, p71_0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [hlam, p71_0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h66, hc45, hlam, hphi, ht01, ht0b, ht5b, p71_1, u1elo2]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h1, h66, hc45, hlam, hphi, ht34, p71_1, u3ehi4]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h66, h70, hlam, p71_1]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h69, hlam, p71_0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [h70, hlam, p71_0]
                          · have p71_0 := h71c.1
                            have p71_1 := h71c.2.1
                            have p71_2 := h71c.2.2.1
                            have p71_3 := h71c.2.2.2
                            linarith only [hlam, p71_0]
                        · linarith only [h70, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                      · linarith only [h62, h69, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h1, h66, h68, hlam, hphi, ht34, ht45, u3ehi2, u5elo0]
                  · linarith only [h60, h66, h67, hc34, hlam, hphi, u3ehi4]
                · linarith only [h66, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
        · linarith only [h59, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h104 | h104
    · rcases m.htr 0 2 5 (by decide) (by decide) with h105 | h105
      · rcases m.htr 0 3 5 (by decide) (by decide) with h106 | h106
        · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
          · rcases m.htr 1 2 4 (by decide) (by decide) with h108 | h108
            · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
              · rcases m.htr 1 3 5 (by decide) (by decide) with h110 | h110
                · linarith only [h0, h104, h110, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi4]
                · linarith only [h106, h110, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
              · linarith only [h0, h109, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h114 | h114
              · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                · linarith only [h0, h104, h108, h115, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h115, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · linarith only [h0, h114, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
            · rcases m.htr 1 2 5 (by decide) (by decide) with h120 | h120
              · rcases m.htr 1 3 5 (by decide) (by decide) with h121 | h121
                · linarith only [h0, h104, h107, h121, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h107, h121, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h104, h106, h120, hlam, hphi, ht34, ht45, u3ehi4, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
              · rcases m.htr 1 3 5 (by decide) (by decide) with h126 | h126
                · linarith only [h0, h104, h126, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi4]
                · linarith only [h0, h106, h107, h126, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
              · linarith only [h0, h104, h106, h125, hlam, hphi, ht34, ht45, u3ehi4, u5elo2]
        · linarith only [h106, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
      · linarith only [h0, h104, h105, hc15, hlam, hphi, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h132 | h132
      · rcases m.htr 0 3 5 (by decide) (by decide) with h133 | h133
        · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
          · rcases m.htr 1 2 4 (by decide) (by decide) with h135 | h135
            · rcases m.htr 1 2 5 (by decide) (by decide) with h136 | h136
              · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
                · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                  · linarith only [h134, h138, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h140 | h140
                    · linarith only [h135, h138, h140, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi4]
                    · linarith only [h133, h140, hlam, hphi, ht34, ht45, u3ehi2, u5elo0]
                · linarith only [h104, h133, h137, hlam, hphi, ht34, ht45, u3ehi1, u5elo1]
              · linarith only [h135, h136, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h145 | h145
              · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
                · rcases m.htr 2 3 4 (by decide) (by decide) with h147 | h147
                  · linarith only [h134, h135, h147, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h134, h135, h147, hc34, hlam, hphi, u3ehi2]
                · linarith only [h146, hlam, hphi, ht34, ht45, u3ehi1, u5elo3]
              · linarith only [h0, h145, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h152 | h152
            · rcases m.htr 1 2 5 (by decide) (by decide) with h153 | h153
              · rcases m.htr 1 3 5 (by decide) (by decide) with h154 | h154
                · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h158 | h158
                        · rcases h5bigk with h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h104, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h104, hc25, hlam, hphi, p159_1, u5elo1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h104, hlam, hphi, ht34, ht45, p159_1, u3ehi4, u5elo1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h104, hc45, hlam, hphi, p159_1, u5elo1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hc05, hlam, hphi, p159_1, u5elo1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h156, hlam, hphi, ht34, ht45, p159_1, u3ehi4, u5elo1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, hphi, ht34, ht45, p159_1, u3ehi4, u5elo1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hc45, hlam, hphi, p159_1, u5elo1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h132, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h153, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h132, hlam, hphi, ht34, ht45, p159_1, u3ehi4, u5elo0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, h132, h134, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h133, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h154, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h156, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hc45, hlam, hphi, p159_1, u5elo3]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hc05, hlam, hphi, p159_1, u5elo4]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h134, h152, h155, h158, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h157, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h158, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                        · linarith only [h158, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                      · linarith only [h155, h157, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                    · linarith only [h0, h134, h156, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h132, h133, h134, h155, hc34, hlam, hphi, u3ehi4]
                · linarith only [h133, h154, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
              · linarith only [h0, h132, h133, h153, hlam, hphi, ht34, ht45, u3ehi4, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h191 | h191
              · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h195 | h195
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h196 | h196
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
                            linarith only [h104, hlam, p197_1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h194, hlam, hphi, ht34, ht45, p197_1, u3ehi4, u5elo0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h104, hlam, hphi, ht34, ht45, p197_1, u3ehi4, u5elo1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h104, hc45, hlam, hphi, p197_1, u5elo1]
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
                            linarith only [h194, hlam, hphi, ht34, ht45, p197_1, u3ehi4, u5elo1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, hphi, ht34, ht45, p197_1, u3ehi4, u5elo1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hc45, hlam, hphi, p197_1, u5elo1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h132, hlam, p197_1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h191, hlam, p197_1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h0, h132, h152, h193, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p197_1, u3ehi4]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h0, h132, h152, h193, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p197_1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h133, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h192, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h194, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hc45, hlam, hphi, p197_1, u5elo3]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hc05, hlam, hphi, p197_1, u5elo4]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h0, h132, h152, h193, h194, h196, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p197_1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h195, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h196, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                        · linarith only [h196, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
                      · linarith only [h0, h132, h152, h194, h195, hlam, hphi, ht34, ht45, u3ehi4, u5elo4]
                    · linarith only [h0, h152, h193, h194, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h132, h133, h134, h193, hc34, hlam, hphi, u3ehi4]
                · linarith only [h133, h192, hlam, hphi, ht34, ht45, u3ehi1, u5elo0]
              · linarith only [h0, h191, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h133, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h230 | h230
        · rcases m.htr 1 2 3 (by decide) (by decide) with h231 | h231
          · rcases m.htr 1 2 4 (by decide) (by decide) with h232 | h232
            · rcases m.htr 1 2 5 (by decide) (by decide) with h233 | h233
              · linarith only [h0, h132, h233, hc01, hlam, hphi, u1elo1]
              · linarith only [h232, h233, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h236 | h236
              · linarith only [h0, h132, h236, hc01, hlam, hphi, u1elo1]
              · linarith only [h0, h236, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h239 | h239
            · rcases m.htr 1 2 5 (by decide) (by decide) with h240 | h240
              · linarith only [h0, h132, h240, hc01, hlam, hphi, u1elo1]
              · linarith only [h239, h240, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h243 | h243
              · linarith only [h0, h132, h243, hc01, hlam, hphi, u1elo1]
              · linarith only [h0, h243, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h230, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

theorem r1l7_11_14_25_L_0_L_R_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
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
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                    · linarith only [h10, h2, h8, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                    · linarith only [h10, h7, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h13, h4, h7, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h0, h15, h4, h7, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
                      · linarith only [h1, h17, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h0, h17, h19, h4, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h2, h21, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h21, hlam, hphi, ht45, u4ehi1, u5elo4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
                · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h25, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                    · linarith only [h2, h25, h27, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                    · linarith only [h0, h24, h27, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
                  · linarith only [h0, h24, h30, h4, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
                    · linarith only [h0, h24, h32, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
                      · linarith only [h1, h34, h6, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                        · linarith only [h1, h36, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h38 | h38
                          · linarith only [h2, h38, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                          · linarith only [h38, hlam, hphi, ht45, u4ehi1, u5elo4]
            · linarith only [h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h42 | h42
            · rcases m.htr 0 3 4 (by decide) (by decide) with h43 | h43
              · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                · linarith only [h4, h42, h44, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi7]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
                  · linarith only [h0, h46, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                    · linarith only [h1, h44, h48, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                    · linarith only [h4, h42, h48, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
                · linarith only [h4, h42, h51, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi7]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
                  · linarith only [h1, h51, h53, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
                    · linarith only [h1, h51, h55, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                    · linarith only [h4, h42, h55, hc12, hc23, hlam, hphi]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
              · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                · linarith only [h0, h42, h59, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h61 | h61
                  · linarith only [h0, h42, h61, hlam, hphi, ht45, u4ehi2, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h63 | h63
                    · linarith only [h0, h42, h63, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
                      · linarith only [h1, h65, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h67 | h67
                        · linarith only [h58, h65, h67, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h69 | h69
                          · linarith only [h2, h69, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h69, hlam, hphi, ht45, u4ehi1, u5elo4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                · linarith only [h0, h42, h72, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                  · linarith only [h0, h74, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
                    · linarith only [h0, h42, h76, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
                      · linarith only [h1, h58, h78, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h80 | h80
                        · linarith only [h1, h80, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                          · linarith only [h2, h82, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                          · linarith only [h82, hlam, hphi, ht45, u4ehi1, u5elo4]
        · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h86 | h86
        · linarith only [h2, h86, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi6]
        · linarith only [h1, h86, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
      · linarith only [h1, h89, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h91 | h91
        · linarith only [h1, h91, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi6]
        · linarith only [h0, h91, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h94 | h94
    · rcases m.htr 0 1 4 (by decide) (by decide) with h95 | h95
      · linarith only [h0, h95, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h97 | h97
        · linarith only [h0, h97, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi6]
        · linarith only [h94, h97, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h100 | h100
      · linarith only [h100, h94, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h102 | h102
        · linarith only [h102, h94, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi6]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h104 | h104
          · rcases m.htr 0 2 5 (by decide) (by decide) with h105 | h105
            · rcases m.htr 0 3 4 (by decide) (by decide) with h106 | h106
              · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
                · rcases m.htr 1 2 4 (by decide) (by decide) with h108 | h108
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h111 | h111
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h112 | h112
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                            · linarith only [h0, h104, h113, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h115 | h115
                              · linarith only [h106, h113, h115, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h117 | h117
                                · linarith only [h106, h107, h117, h94, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                                · linarith only [h112, h113, h117, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                          · linarith only [h112, hlam, hphi, ht45, u4ehi1, u5elo4]
                        · linarith only [h111, h94, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h106, h110, h94, hlam]
                    · linarith only [h108, h109, hlam, hphi, ht45, u4ehi2, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h125 | h125
                      · linarith only [h107, h108, h125, hlam]
                      · linarith only [h0, h104, h106, h108, h125, h94, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h105, h124, hlam]
                · linarith only [h0, h104, h107, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h130 | h130
                · rcases m.htr 1 2 4 (by decide) (by decide) with h131 | h131
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h132 | h132
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
                      · linarith only [h106, h133, h94, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h135 | h135
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h136 | h136
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
                            · linarith only [h133, h135, h137, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                              · linarith only [h0, h104, h139, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
                              · linarith only [h133, h135, h139, hc23, hc34, hlam, hphi]
                          · linarith only [h136, hlam, hphi, ht45, u4ehi1, u5elo4]
                        · linarith only [h135, h94, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h0, h105, h132, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h145 | h145
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                      · linarith only [h106, h146, h94, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h148 | h148
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h149 | h149
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h150 | h150
                            · linarith only [h146, h148, h150, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h152 | h152
                              · linarith only [h0, h104, h131, h150, h152, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                              · linarith only [h130, h131, h148, h150, h152, hc23, hc34, hlam, hphi]
                          · linarith only [h149, hlam, hphi, ht45, u4ehi1, u5elo4]
                        · linarith only [h148, h94, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h0, h145, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h104, h130, hlam]
            · linarith only [h104, h105, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h160 | h160
            · rcases m.htr 0 3 4 (by decide) (by decide) with h161 | h161
              · rcases m.htr 1 2 3 (by decide) (by decide) with h162 | h162
                · linarith only [h104, h160, h162, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi7]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h165 | h165
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h166 | h166
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h167 | h167
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h168 | h168
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h170 | h170
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h171 | h171
                                · linarith only [h164, h169, h171, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                                · linarith only [h168, h171, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
                              · linarith only [h162, h164, h170, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                            · linarith only [h161, h162, h164, h168, h169, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h100, h168, hlam, hphi, ht45, u4ehi0, u5elo4]
                        · linarith only [h167, h94, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h100, h104, h160, h161, h166, h94, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi7]
                    · linarith only [h100, h104, h160, h164, h165, h94, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h180 | h180
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h182 | h182
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                                · linarith only [h161, h186, h94, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi4]
                                · linarith only [h186, hlam, hphi, ht45, u4ehi3, u5elo4]
                              · linarith only [h104, h185, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                            · linarith only [h0, h162, h184, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h100, h183, hlam, hphi, ht45, u4ehi0, u5elo4]
                        · linarith only [h161, h182, h94, hlam, hphi, ht45, u4ehi3, u5elo3]
                      · linarith only [h161, h181, h94, hlam]
                    · linarith only [h0, h160, h180, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                · linarith only [h104, h160, h195, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi7]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h197 | h197
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h198 | h198
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h199 | h199
                      · linarith only [h104, h160, h161, h199, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi7]
                      · linarith only [h195, h197, h199, hlam]
                    · linarith only [h160, h197, h198, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h203 | h203
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h204 | h204
                      · linarith only [h104, h160, h161, h204, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi7]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h206 | h206
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h207 | h207
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h208 | h208
                            · linarith only [h204, h206, h208, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                            · linarith only [h104, h160, h208, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                          · linarith only [h0, h160, h195, h204, h207, hlam, hphi, u5ehi7, u5elo4]
                        · linarith only [h0, h160, h195, h206, hlam, hphi, u5ehi7, u5elo3]
                    · linarith only [h0, h160, h203, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h214 | h214
              · rcases m.htr 1 2 3 (by decide) (by decide) with h215 | h215
                · linarith only [h104, h214, h215, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h217 | h217
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h218 | h218
                    · linarith only [h160, h215, h218, hc02, hc23, hlam, hphi]
                    · linarith only [h100, h217, h218, hlam, hphi, ht45, u4ehi0, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
                    · linarith only [h0, h160, h221, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h221, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
                · linarith only [h0, h104, h224, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h226 | h226
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h227 | h227
                    · linarith only [h0, h160, h227, hc01, hlam, hphi, u1elo1]
                    · linarith only [h226, h227, hlam, hphi, ht45, u4ehi1, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h230 | h230
                    · linarith only [h0, h160, h230, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h230, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem r1l7_11_23_L_I_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_L m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h1, h11, h13, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                            · linarith only [h1, h10, h13, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                          · linarith only [h12, hc23, hlam, hphi, u3elo4]
                        · linarith only [h11, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                            · linarith only [h10, h20, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · rcases h1bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h19, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                rcases p22_3 (m.d 0 1) (by simp) with h25 | h25
                                · rcases p22_3 (m.d 1 2) (by simp) with h26 | h26
                                  · linarith only [h0, h26, hlam]
                                  · linarith only [h26, h6, hlam]
                                · linarith only [h25, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                rcases p22_3 (m.d 0 1) (by simp) with h30 | h30
                                · rcases p22_3 (m.d 1 2) (by simp) with h31 | h31
                                  · linarith only [h0, h31, hlam]
                                  · linarith only [h10, h19, h20, h31, h6, hc34, hc45, hlam, hphi]
                                · linarith only [h30, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                rcases p22_3 (m.d 0 1) (by simp) with h35 | h35
                                · rcases p22_3 (m.d 1 2) (by simp) with h36 | h36
                                  · linarith only [h0, h36, hlam]
                                  · linarith only [h36, h7, hlam]
                                · linarith only [h35, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h0, h19, h20, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                rcases p22_3 (m.d 0 1) (by simp) with h43 | h43
                                · rcases p22_3 (m.d 1 2) (by simp) with h44 | h44
                                  · rcases p22_3 (m.d 1 3) (by simp) with h45 | h45
                                    · linarith only [h45, h6, hlam]
                                    · linarith only [h45, h8, hlam]
                                  · linarith only [h44, hlam, p22_0]
                                · linarith only [h2, h43, hlam]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                rcases p22_3 (m.d 0 1) (by simp) with h50 | h50
                                · rcases p22_3 (m.d 1 2) (by simp) with h51 | h51
                                  · rcases p22_3 (m.d 1 3) (by simp) with h52 | h52
                                    · linarith only [h52, h6, hlam]
                                    · linarith only [h52, h9, hlam]
                                  · linarith only [h51, h7, hlam]
                                · linarith only [h3, h50, hlam]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h1, hlam, p22_0]
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
                                linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p22_1, u3elo1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p22_1, u3elo0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h2, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h19, h2, h20, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h8, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h10, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h3, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h7, hlam, p22_1]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h9, hlam, p22_0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [h3, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p22_1, u3elo0]
                              · have p22_0 := h22c.1
                                have p22_1 := h22c.2.1
                                have p22_2 := h22c.2.2.1
                                have p22_3 := h22c.2.2.2
                                linarith only [hlam, p22_0]
                          · linarith only [h19, hc23, hlam, hphi, u3elo4]
                        · linarith only [h18, hc23, hlam, hphi, u3elo3]
                    · linarith only [h9, hc13, hlam, hphi, u3elo4]
                  · linarith only [h6, h8, hc23, hlam, hphi, u3elo3]
                · linarith only [h3, h5, h6, h7, hc23, hlam, hphi, u3elo0]
              · linarith only [h6, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h5, hc03, hlam, hphi, u3elo4]
          · linarith only [h4, hc02, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h80 | h80
          · rcases m.htr 0 3 5 (by decide) (by decide) with h81 | h81
            · linarith only [h0, h3, h81, hc12, hlam, hphi, ht23, u3elo0]
            · linarith only [h81, hc03, hlam, hphi, u3elo4]
          · linarith only [h80, hc02, hlam, hphi, ht23, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h85 | h85
        · rcases m.htr 0 2 3 (by decide) (by decide) with h86 | h86
          · rcases m.htr 0 3 5 (by decide) (by decide) with h87 | h87
            · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
              · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
                · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                  · linarith only [h0, h1, h2, h88, h90, hc23, hlam, hphi, u3elo0]
                  · linarith only [h90, hc13, hlam, hphi, u3elo3]
                · linarith only [h85, h87, h88, h89, hc23, hlam, hphi, u3elo0]
              · linarith only [h88, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h87, hc03, hlam, hphi, u3elo4]
          · linarith only [h86, hc02, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h97 | h97
          · rcases m.htr 0 3 5 (by decide) (by decide) with h98 | h98
            · linarith only [h0, h85, h98, hc12, hlam, hphi, ht23, u3elo0]
            · linarith only [h98, hc03, hlam, hphi, u3elo4]
          · linarith only [h97, hc02, hlam, hphi, ht23, u3elo2]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h103 | h103
    · rcases m.htr 0 1 4 (by decide) (by decide) with h104 | h104
      · rcases m.htr 0 1 5 (by decide) (by decide) with h105 | h105
        · rcases m.htr 0 2 3 (by decide) (by decide) with h106 | h106
          · rcases m.htr 0 3 5 (by decide) (by decide) with h107 | h107
            · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
              · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h111 | h111
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h112 | h112
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h114 | h114
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h115 | h115
                            · linarith only [h0, h103, h108, h113, h115, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h103, h110, h112, h115, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                          · linarith only [h114, hc23, hlam, hphi, u3elo4]
                        · linarith only [h113, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h121 | h121
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                            · linarith only [h112, h122, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · rcases h1bigk with h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h0, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h0, h108, h121, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                rcases p124_3 (m.d 0 1) (by simp) with h128 | h128
                                · rcases p124_3 (m.d 1 2) (by simp) with h129 | h129
                                  · rcases p124_3 (m.d 1 3) (by simp) with h130 | h130
                                    · linarith only [h103, h130, hlam]
                                    · linarith only [h110, h130, hlam]
                                  · linarith only [h0, h103, h108, h112, h121, h122, h129, hc34, hc45, hlam, hphi]
                                · linarith only [h128, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                rcases p124_3 (m.d 0 1) (by simp) with h135 | h135
                                · rcases p124_3 (m.d 1 2) (by simp) with h136 | h136
                                  · rcases p124_3 (m.d 1 3) (by simp) with h137 | h137
                                    · linarith only [h103, h137, hlam]
                                    · linarith only [h111, h137, hlam]
                                  · linarith only [h109, h136, hlam]
                                · linarith only [h135, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h103, h108, h121, h122, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                rcases p124_3 (m.d 0 1) (by simp) with h144 | h144
                                · linarith only [h0, h144, hlam]
                                · linarith only [h103, h144, hlam]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                rcases p124_3 (m.d 0 1) (by simp) with h147 | h147
                                · linarith only [h0, h147, hlam]
                                · linarith only [h104, h147, hlam]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                rcases p124_3 (m.d 0 1) (by simp) with h150 | h150
                                · linarith only [h0, h150, hlam]
                                · linarith only [h105, h150, hlam]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h103, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h108, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h103, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p124_1, u3elo0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h103, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p124_1, u3elo0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h104, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h110, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h112, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h105, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h109, hlam, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h111, hlam, p124_0]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [h0, h105, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p124_1]
                              · have p124_0 := h124c.1
                                have p124_1 := h124c.2.1
                                have p124_2 := h124c.2.2.1
                                have p124_3 := h124c.2.2.2
                                linarith only [hlam, p124_0]
                          · linarith only [h103, h111, h120, h121, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · linarith only [h120, hc23, hlam, hphi, u3elo3]
                    · linarith only [h111, hc13, hlam, hphi, u3elo4]
                  · linarith only [h108, h110, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h105, h109, hlam]
              · linarith only [h0, h108, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h107, hc03, hlam, hphi, u3elo4]
          · linarith only [h0, h103, h106, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h176 | h176
          · rcases m.htr 0 3 5 (by decide) (by decide) with h177 | h177
            · linarith only [h103, h105, h177, hc13, hlam, hphi, u3elo0]
            · linarith only [h177, hc03, hlam, hphi, u3elo4]
          · linarith only [h0, h103, h176, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h181 | h181
        · rcases m.htr 0 2 3 (by decide) (by decide) with h182 | h182
          · rcases m.htr 0 3 5 (by decide) (by decide) with h183 | h183
            · rcases m.htr 1 2 3 (by decide) (by decide) with h184 | h184
              · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
                · rcases m.htr 1 3 4 (by decide) (by decide) with h186 | h186
                  · linarith only [h103, h104, h186, hc01, hlam, hphi, ht12, ht23, u3elo0]
                  · linarith only [h184, h186, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h181, h185, hlam]
              · linarith only [h0, h103, h184, hc13, hlam, hphi, u3elo2]
            · linarith only [h182, h183, hc23, hlam, hphi, u3elo4]
          · linarith only [h182, hc02, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h193 | h193
          · rcases m.htr 0 3 5 (by decide) (by decide) with h194 | h194
            · linarith only [h103, h181, h194, hc13, hlam, hphi, u3elo0]
            · linarith only [h194, hc03, hlam, hphi, u3elo4]
          · linarith only [h0, h103, h193, hc13, hlam, hphi, u3elo2]
    · linarith only [h103, hc01, hlam, hphi, ht12, ht23, u3elo1]

theorem r1l7_11_23_L_I_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                    · linarith only [h1, h10, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h10, hc34, hlam, hphi, u3ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                    · linarith only [h1, h13, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h13, hc34, hlam, hphi, u3ehi1]
              · linarith only [h4, h6, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h5, hc35, hlam, hphi, u3ehi0]
          · linarith only [h1, h4, hc34, hlam, hphi, u3ehi1]
        · linarith only [h1, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
      · linarith only [h1, h2, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h21 | h21
      · rcases m.htr 0 1 5 (by decide) (by decide) with h22 | h22
        · rcases m.htr 0 3 4 (by decide) (by decide) with h23 | h23
          · rcases m.htr 0 3 5 (by decide) (by decide) with h24 | h24
            · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
              · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                · linarith only [h0, h1, h26, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                    · linarith only [h1, h21, h26, h29, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h1, h23, h29, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                    · linarith only [h1, h21, h26, h32, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h23, h32, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h23, h25, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h24, hc35, hlam, hphi, u3ehi0]
          · linarith only [h23, hc34, hlam, hphi, u3ehi0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h38 | h38
          · rcases m.htr 0 3 5 (by decide) (by decide) with h39 | h39
            · rcases m.htr 0 4 5 (by decide) (by decide) with h40 | h40
              · linarith only [h21, h22, h40, hlam]
              · linarith only [h38, h40, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h38, h39, hc35, hlam, hphi, u3ehi3]
          · linarith only [h38, hc34, hlam, hphi, u3ehi0]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h45 | h45
        · rcases m.htr 0 3 4 (by decide) (by decide) with h46 | h46
          · rcases m.htr 0 3 5 (by decide) (by decide) with h47 | h47
            · rcases m.htr 0 4 5 (by decide) (by decide) with h48 | h48
              · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                · linarith only [h0, h21, h49, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
                      · linarith only [h0, h21, h49, h51, h52, h53, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h0, h21, h52, h53, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h46, h52, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                      · linarith only [h21, h45, h58, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h1, h58, hc35, hlam, hphi, u3ehi0]
                    · linarith only [h1, h45, h46, h47, h57, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · linarith only [h21, h45, h47, h48, hc45, hlam, hphi, ht34, u3ehi4]
            · linarith only [h47, hc35, hlam, hphi, u3ehi0]
          · linarith only [h46, hc34, hlam, hphi, u3ehi0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h65 | h65
          · rcases m.htr 0 3 5 (by decide) (by decide) with h66 | h66
            · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
              · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
                · linarith only [h0, h68, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
                  · linarith only [h0, h45, h70, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h73 | h73
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h74 | h74
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
                            · rcases h1bigk with h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h45, h68, h72, h74, hc12, hc23, hlam, hphi, p77_1]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h1, hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h21, hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h45, hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h0, hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h68, hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h45, h74, hc01, hc12, hlam, hphi, p77_1]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h70, hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h0, h68, hc12, hc23, hlam, hphi, p77_1]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                rcases p77_3 (m.d 0 1) (by simp) with h89 | h89
                                · linarith only [h1, h89, hlam]
                                · linarith only [h0, h89, hlam]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h0, h21, h68, hc12, hc23, hlam, hphi, p77_1]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h0, h45, h68, hc12, hc23, hlam, hphi, p77_1]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h0, h68, h72, hc12, hc23, hlam, hphi, p77_1]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                rcases p77_3 (m.d 0 1) (by simp) with h96 | h96
                                · linarith only [h21, h96, hlam]
                                · linarith only [h0, h96, hlam]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h72, hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h0, h45, h68, h72, hc12, hc23, hlam, hphi, p77_1]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h0, h70, hc12, hc25, hlam, hphi, p77_1]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                rcases p77_3 (m.d 0 1) (by simp) with h103 | h103
                                · linarith only [h103, h45, hlam]
                                · linarith only [h0, h103, hlam]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h73, hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [h74, hlam, p77_0]
                              · have p77_0 := h77c.1
                                have p77_1 := h77c.2.1
                                have p77_2 := h77c.2.2.1
                                have p77_3 := h77c.2.2.2
                                linarith only [hlam, p77_0]
                            · linarith only [h76, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h1, h68, h75, hc35, hlam, hphi, u3ehi0]
                        · linarith only [h0, h1, h21, h65, h67, h68, h74, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h66, h73, hlam]
                    · linarith only [h1, h65, h72, hlam]
              · linarith only [h65, h67, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h65, h66, hc35, hlam, hphi, u3ehi3]
          · linarith only [h65, hc34, hlam, hphi, u3ehi0]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h117 | h117
    · linarith only [h0, h117, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h119 | h119
      · rcases m.htr 0 1 5 (by decide) (by decide) with h120 | h120
        · rcases m.htr 0 3 4 (by decide) (by decide) with h121 | h121
          · rcases m.htr 0 3 5 (by decide) (by decide) with h122 | h122
            · rcases m.htr 0 4 5 (by decide) (by decide) with h123 | h123
              · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
                · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                    · linarith only [h117, h119, h124, h126, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h121, h126, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h117, h119, h122, h123, h124, h125, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h119, h122, h123, h124, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
              · linarith only [h121, h123, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h121, h122, hc35, hlam, hphi, u3ehi3]
          · linarith only [h121, hc34, hlam, hphi, u3ehi0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h134 | h134
          · rcases m.htr 0 3 5 (by decide) (by decide) with h135 | h135
            · rcases m.htr 0 4 5 (by decide) (by decide) with h136 | h136
              · linarith only [h119, h120, h136, hlam]
              · linarith only [h134, h136, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h134, h135, hc35, hlam, hphi, u3ehi3]
          · linarith only [h134, hc34, hlam, hphi, u3ehi0]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h141 | h141
        · rcases m.htr 0 3 4 (by decide) (by decide) with h142 | h142
          · rcases m.htr 0 3 5 (by decide) (by decide) with h143 | h143
            · rcases m.htr 0 4 5 (by decide) (by decide) with h144 | h144
              · rcases m.htr 1 2 3 (by decide) (by decide) with h145 | h145
                · rcases m.htr 1 2 5 (by decide) (by decide) with h146 | h146
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h147 | h147
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h148 | h148
                      · linarith only [h119, h141, h145, h147, h148, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h148, hc35, hlam, hphi, u3ehi1]
                    · linarith only [h117, h141, h142, h143, h147, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h117, h141, h143, h145, h146, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h141, h143, h145, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
              · linarith only [h119, h141, h143, h144, hc45, hlam, hphi, ht34, u3ehi4]
            · linarith only [h143, hc35, hlam, hphi, u3ehi0]
          · linarith only [h142, hc34, hlam, hphi, u3ehi0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h157 | h157
          · rcases m.htr 0 3 5 (by decide) (by decide) with h158 | h158
            · rcases m.htr 0 4 5 (by decide) (by decide) with h159 | h159
              · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
                · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h163 | h163
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h165 | h165
                          · linarith only [h160, h165, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h165, hc35, hlam, hphi, u3ehi2]
                        · linarith only [h119, h159, h164, hlam]
                      · linarith only [h117, h158, h163, hlam]
                    · linarith only [h117, h162, hc34, hlam, hphi, u3ehi0]
                  · linarith only [h160, h161, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h174 | h174
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h176 | h176
                          · linarith only [h160, h172, h176, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h176, hc35, hlam, hphi, u3ehi2]
                        · linarith only [h119, h159, h175, hlam]
                      · linarith only [h117, h158, h174, hlam]
                    · linarith only [h117, h157, h173, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h182 | h182
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h184 | h184
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h185 | h185
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                            · rcases h1bigk with h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h0, hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h117, hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h119, hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h141, hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h172, h185, hc01, hc23, hlam, hphi, ht12, p187_1]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h160, hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h119, h172, h185, hc01, hc23, hlam, hphi, ht12, p187_1]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h172, hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                rcases p187_3 (m.d 0 1) (by simp) with h198 | h198
                                · linarith only [h198, hlam, p187_0]
                                · rcases p187_3 (m.d 1 2) (by simp) with h200 | h200
                                  · linarith only [h160, h200, hlam]
                                  · linarith only [h0, h200, hlam]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p187_1]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h119, h157, h160, h186, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p187_1, u3ehi4]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h141, h158, h160, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p187_1, u3ehi4]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                rcases p187_3 (m.d 0 1) (by simp) with h207 | h207
                                · linarith only [h207, hlam, p187_0]
                                · rcases p187_3 (m.d 1 2) (by simp) with h209 | h209
                                  · linarith only [h160, h209, hc01, hc23, hlam, hphi, ht12, p187_1]
                                  · linarith only [h0, h209, hlam]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p187_1]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h182, hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h141, h158, h160, h182, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p187_1, u3ehi4]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                rcases p187_3 (m.d 0 1) (by simp) with h216 | h216
                                · linarith only [h216, hlam, p187_0]
                                · rcases p187_3 (m.d 1 2) (by simp) with h218 | h218
                                  · linarith only [h172, h218, hlam]
                                  · linarith only [h0, h218, hlam]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p187_1]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h183, hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [h184, hlam, p187_0]
                              · have p187_0 := h187c.1
                                have p187_1 := h187c.2.1
                                have p187_2 := h187c.2.2.1
                                have p187_3 := h187c.2.2.2
                                linarith only [hlam, p187_0]
                            · linarith only [h186, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h160, h185, hc35, hlam, hphi, u3ehi1]
                        · linarith only [h119, h157, h184, hc45, hlam, hphi, ht34, u3ehi3]
                      · linarith only [h117, h183, hc35, hlam, hphi, u3ehi0]
                    · linarith only [h117, h157, h182, hlam]
              · linarith only [h157, h159, hc45, hlam, hphi, ht34, u3ehi3]
            · linarith only [h158, hc35, hlam, hphi, u3ehi0]
          · linarith only [h157, hc34, hlam, hphi, u3ehi0]

end R2N4
