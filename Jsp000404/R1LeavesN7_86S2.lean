import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_R_L_R_L_0_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
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
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · rcases h5bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc15, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc25, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc35, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc45, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc05, hlam, hphi, p12_1, u5elo1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, hphi, ht23, ht34, ht45, p12_1, u2ehi4, u5elo1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h11, hc45, hlam, hphi, p12_1, u5elo1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc45, hlam, hphi, p12_1, u5elo1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h6, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, h11, hc45, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, hc45, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h2, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h7, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h9, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc45, hlam, hphi, p12_1, u5elo3]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h3, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, hphi, ht12, ht23, ht34, p12_1, u1ehi4, u4elo4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h10, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h11, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                        · linarith only [h10, h11, h5, hc34, hlam, hphi, u4elo1]
                      · linarith only [h10, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
                    · linarith only [h9, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                  · linarith only [h8, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
                · linarith only [h2, h7, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo0]
              · linarith only [h1, h6, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo0]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
            · linarith only [h4, h45, hc23, hlam, hphi, u2ehi3]
            · linarith only [h45, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
          · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
            · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
              · rcases m.htr 1 3 5 (by decide) (by decide) with h51 | h51
                · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
                      · linarith only [h1, h3, h49, h54, hlam, hphi, ht23, ht34, u2ehi4, u4elo1]
                      · linarith only [h54, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
                    · linarith only [h53, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                  · linarith only [h52, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
                · linarith only [h51, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
              · linarith only [h1, h50, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo0]
            · linarith only [h48, h49, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
            · linarith only [h48, h62, hc23, hlam, hphi, u2ehi3]
            · linarith only [h62, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
      · linarith only [h0, h2, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
    · linarith only [h1, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h67 | h67
    · linarith only [h0, h67, hc23, hlam, hphi, u2ehi4]
    · linarith only [h67, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_11_12_14_25_L_R_L_R_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
            · linarith only [h4, h5, hc25, hlam, hphi, u2ehi3]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h3, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
              · linarith only [h1, h10, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h13, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h12, h13, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                  · linarith only [h12, h16, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h10, h18, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · linarith only [h18, h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h22 | h22
        · linarith only [h2, h22, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
          · linarith only [h0, h2, h24, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
            · linarith only [h0, h26, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h28 | h28
              · linarith only [h1, h28, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h32 | h32
                    · linarith only [h24, h28, h30, h32, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h22, h32, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h0, h2, h31, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h0, h2, h30, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h38 | h38
    · linarith only [h0, h38, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h40 | h40
      · rcases m.htr 0 2 4 (by decide) (by decide) with h41 | h41
        · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
          · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
            · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
              · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                · rcases m.htr 2 3 5 (by decide) (by decide) with h46 | h46
                  · linarith only [h40, h46, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h48 | h48
                    · linarith only [h45, h46, h48, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h50 | h50
                      · linarith only [h48, h50, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h42, h44, h45, h46, h50, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                  · linarith only [h45, h53, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h55 | h55
                    · linarith only [h0, h41, h55, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h57 | h57
                      · linarith only [h45, h55, h57, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h42, h44, h45, h57, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h38, h44, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
            · linarith only [h0, h41, h43, hc25, hlam, hphi, u2ehi3]
          · linarith only [h0, h41, h42, hlam]
        · linarith only [h40, h41, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h64 | h64
        · linarith only [h40, h64, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
          · linarith only [h0, h64, h66, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h66, hc24, hlam, hphi, ht12, u1ehi0]

theorem r1l7_11_12_25_L_0_L_R_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi3]
            · linarith only [h0, h2, h6, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h10 | h10
        · linarith only [h10, h2, hc24, hlam, hphi, u2ehi4]
        · linarith only [h10, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
    · linarith only [h0, h1, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h14 | h14
    · rcases m.htr 0 2 4 (by decide) (by decide) with h15 | h15
      · rcases m.htr 0 2 5 (by decide) (by decide) with h16 | h16
        · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
          · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h14, h19, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi4]
              · linarith only [h17, h19, hc25, hlam, hphi, u2ehi2]
            · linarith only [h0, h15, h18, hlam]
          · linarith only [h0, h14, h16, h17, hc23, hlam, hphi, u2ehi4]
        · linarith only [h15, h16, hc25, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h25 | h25
        · linarith only [h15, h25, hc24, hlam, hphi, u2ehi4]
        · linarith only [h25, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h28 | h28
      · rcases m.htr 0 2 5 (by decide) (by decide) with h29 | h29
        · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
          · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
            · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
              · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
                        · linarith only [h30, h34, h37, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h0, h28, h36, h37, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h36, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                    · linarith only [h34, h35, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h42 | h42
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
                        · rcases h5bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h14, hlam, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hlam, hphi, ht23, ht34, ht45, p45_1, u2ehi4, u5elo0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h14, hc35, hlam, hphi, p45_1, u5elo1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h14, hc45, hlam, hphi, p45_1, u5elo1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hc05, hlam, hphi, p45_1, u5elo1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hlam, hphi, ht23, ht34, ht45, p45_1, u2ehi4, u5elo1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h44, hc45, hlam, hphi, p45_1, u5elo1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hc45, hlam, hphi, p45_1, u5elo1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h29, hlam, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h32, hlam, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h0, h28, h34, h42, h44, hc45, hlam, hphi, ht01, ht0b, ht5b, p45_1, u1elo1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h0, h28, h34, h42, hc45, hlam, hphi, ht01, ht0b, ht5b, p45_1, u1elo1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h29, hc35, hlam, hphi, ht23, p45_1, u2ehi4]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h33, hlam, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h42, hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h0, h28, h34, h42, hc45, hlam, hphi, ht01, ht0b, ht5b, p45_1, u1elo1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h29, hc45, hlam, hphi, ht23, ht34, p45_1, u2ehi4]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h0, h14, h28, h34, h42, h44, hc01, hlam, hphi, p45_1, u1elo1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h43, hlam, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h44, hlam, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hlam, p45_0]
                        · linarith only [h34, h42, h44, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                      · linarith only [h34, h42, h43, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                    · linarith only [h42, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                · linarith only [h30, h33, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
              · linarith only [h0, h28, h32, hc25, hlam, hphi, u2ehi3]
            · linarith only [h0, h28, h31, hlam]
          · linarith only [h0, h28, h30, hc23, hlam, hphi, u2ehi3]
        · linarith only [h28, h29, hc25, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h79 | h79
        · linarith only [h28, h79, hc24, hlam, hphi, u2ehi4]
        · linarith only [h79, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem r1l7_11_12_25_L_R_L_R_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · rcases h5bigk with h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc15, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc25, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc35, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc45, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, hphi, ht23, ht34, ht45, p8_1, u2ehi4, u5elo1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, h7, hc45, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, hc45, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, hc25, hlam, hphi, ht12, p8_1, u1ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h4, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, h4, h7, hc45, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, h4, hc45, hlam, hphi, p8_1, u5elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, hc35, hlam, hphi, ht12, ht23, p8_1, u1ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p8_1, u1ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8_1, u2ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h3, h5, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h2, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p8_1, u1ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h6, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h7, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                · linarith only [h0, h3, h6, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h6, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
              · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
                · rcases h5bigk with h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hlam, p38_0]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p38_1, u1ehi4, u5elo0]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hlam, hphi, ht23, ht34, ht45, p38_1, u2ehi4, u5elo0]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hc35, hlam, hphi, p38_1, u5elo0]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hc45, hlam, hphi, p38_1, u5elo0]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [h1, hlam, p38_0]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hlam, p38_0]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hlam, hphi, ht23, ht34, ht45, p38_1, u2ehi4, u5elo1]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [h1, h37, hc45, hlam, hphi, p38_1, u5elo0]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [h1, hc45, hlam, hphi, p38_1, u5elo0]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [h1, hc25, hlam, hphi, ht12, p38_1, u1ehi4]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [h4, hlam, p38_1]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hlam, p38_0]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [h1, h37, h4, hc45, hlam, hphi, p38_1, u5elo0]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hc45, hlam, hphi, p38_1, u5elo2]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [h1, hc35, hlam, hphi, ht12, ht23, p38_1, u1ehi4]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p38_1, u1ehi4, u5elo3]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hc25, hlam, hphi, p38_1, u5elo3]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hlam, p38_0]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hc45, hlam, hphi, p38_1, u5elo3]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [h2, hlam, p38_1]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p38_1, u1ehi4]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [h36, hlam, p38_1]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [h37, hlam, p38_1]
                  · have p38_0 := h38c.1
                    have p38_1 := h38c.2.1
                    have p38_2 := h38c.2.2.1
                    have p38_3 := h38c.2.2.2
                    linarith only [hlam, p38_0]
                · linarith only [h0, h3, h36, h37, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h36, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h4, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h67 | h67
          · linarith only [h3, h67, hc24, hlam, hphi, u2ehi4]
          · linarith only [h67, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
        · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
          · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
            · rcases m.htr 2 4 5 (by decide) (by decide) with h73 | h73
              · linarith only [h0, h2, h70, h73, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h73, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h76 | h76
              · linarith only [h0, h1, h2, h70, h76, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
              · linarith only [h76, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
          · linarith only [h71, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
          · linarith only [h70, h80, hc24, hlam, hphi, u2ehi4]
          · linarith only [h80, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h84 | h84
    · linarith only [h0, h84, hc12, hlam, hphi, u1ehi4]
    · linarith only [h84, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem r1l7_11_13_25_L_0_L_0_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h2, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h2, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h6, hc13, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                · linarith only [h11, h12, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h0, h14, h3, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h12, h14, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h11, hc13, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
          · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
            · linarith only [h2, h20, h3, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
              · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                · linarith only [h2, h20, h23, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h2, h23, h3, hc23, hlam, hphi, u3elo3]
              · linarith only [h22, hc13, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h19, h2, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
        · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
          · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
              · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                  · linarith only [h2, h28, h33, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h32, h33, hc34, hlam, hphi, ht45, u5elo4]
                · linarith only [h2, h32, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h2, h28, h31, hc24, hlam, hphi, ht45, u5elo3]
            · linarith only [h2, h28, h30, hlam]
          · linarith only [h28, h29, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
          · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
            · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
              · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
                    · linarith only [h1, h41, h45, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h45, hc34, hlam, hphi, ht45, u5elo4]
                  · linarith only [h28, h44, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h2, h40, h43, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
              · linarith only [h42, hc13, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h51 | h51
              · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                · linarith only [h2, h40, h41, h52, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h2, h40, h52, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
              · linarith only [h2, h40, h51, hc25, hlam, hphi, u5elo3]
          · linarith only [h40, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h58 | h58
    · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
      · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
        · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
          · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
            · linarith only [h0, h58, h62, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
              · linarith only [h0, h58, h64, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · linarith only [h64, hc13, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h0, h61, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
          · rcases m.htr 1 3 4 (by decide) (by decide) with h69 | h69
            · linarith only [h0, h58, h60, h69, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h0, h58, h59, h60, h69, hc23, hlam, hphi, u3elo3]
          · linarith only [h0, h58, h59, h68, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h0, h58, h59, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h74 | h74
      · rcases m.htr 1 2 4 (by decide) (by decide) with h75 | h75
        · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
          · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
            · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
              · rcases m.htr 2 3 4 (by decide) (by decide) with h79 | h79
                · rcases m.htr 2 4 5 (by decide) (by decide) with h80 | h80
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
                    · linarith only [h74, h79, h81, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h81, hc34, hlam, hphi, ht45, u5elo4]
                  · linarith only [h80, hc24, hlam, hphi, ht45, u5elo4]
                · linarith only [h77, h79, hc23, hlam, hphi, u3elo1]
              · linarith only [h58, h78, hc01, hlam, hphi, ht12, ht23, u3elo4]
            · linarith only [h58, h77, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h76, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
          · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
            · linarith only [h74, h75, h90, hlam]
            · linarith only [h58, h90, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h58, h74, h89, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h74, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_11_13_25_L_0_L_0_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h2, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
            · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
            · linarith only [h4, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
              · linarith only [h0, h10, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h10, h12, h3, h8, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h0, h14, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h10, h14, h16, hc23, hlam, hphi, u3elo3]
                    · linarith only [h16, h2, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
          · linarith only [h19, h2, h3, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
            · linarith only [h19, h21, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
              · linarith only [h0, h2, h23, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h2, h23, h3, hc23, hlam, hphi, u3elo3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
        · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
          · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
            · linarith only [h1, h28, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
            · linarith only [h27, h28, hc34, hlam, hphi, ht45, u5elo3]
          · linarith only [h2, h26, h27, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
          · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
            · linarith only [h1, h33, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
            · linarith only [h32, h33, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
            · linarith only [h32, h36, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi8]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
              · linarith only [h2, h32, h38, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h2, h38, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h42 | h42
    · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
      · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
        · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
          · linarith only [h0, h42, h45, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h47 | h47
            · linarith only [h0, h42, h47, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
              · linarith only [h45, h49, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h51 | h51
                · linarith only [h43, h47, h51, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                  · linarith only [h44, h53, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi9]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h55 | h55
                    · linarith only [h49, h53, h55, hc23, hlam, hphi, u3elo3]
                    · linarith only [h43, h45, h55, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
          · linarith only [h0, h42, h44, h58, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h0, h42, h43, h44, h58, hc23, hlam, hphi, u3elo3]
      · linarith only [h0, h43, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
      · rcases m.htr 1 2 4 (by decide) (by decide) with h63 | h63
        · rcases m.htr 1 3 4 (by decide) (by decide) with h64 | h64
          · rcases m.htr 1 3 5 (by decide) (by decide) with h65 | h65
            · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
              · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                · linarith only [h62, h67, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
                · linarith only [h65, h66, h67, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · linarith only [h64, h66, hc23, hlam, hphi, u3elo1]
            · linarith only [h64, h65, hc34, hlam, hphi, ht45, u5elo3]
          · linarith only [h42, h64, hc01, hlam, hphi, ht12, ht23, u3elo3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
          · linarith only [h62, h63, h73, hlam]
          · linarith only [h42, h73, hc01, hlam, hphi, ht12, ht23, u3elo3]
      · linarith only [h0, h62, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_11_13_25_L_R_L_0_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
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
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases h5bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h3, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h3, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h3, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h2, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p13_1]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h2, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h2, h3, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h2, hc25, hlam, hphi, ht12, p13_1, u1ehi4]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h7, hlam, p13_1]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h2, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p13_1]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h0, h11, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p13_1]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h4, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h9, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h11, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo4]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h5, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h10, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h12, hlam, p13_0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13_1, u3elo0]
                            · have p13_0 := h13c.1
                              have p13_1 := h13c.2.1
                              have p13_2 := h13c.2.2.1
                              have p13_3 := h13c.2.2.2
                              linarith only [hlam, p13_0]
                          · rcases h5bigk with h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c | h39c
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h3, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h3, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h12, h3, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h2, hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p39_1]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h2, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h12, h2, h3, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h2, hc25, hlam, hphi, ht12, p39_1, u1ehi4]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h7, hlam, p39_1]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h2, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p39_1]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h12, hlam, p39_1]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h4, hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h9, hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h11, hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h12, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p39_1, u3elo4]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h5, hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h10, hlam, p39_0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h3, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [h1, h10, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p39_1, u3elo0]
                            · have p39_0 := h39c.1
                              have p39_1 := h39c.2.1
                              have p39_2 := h39c.2.2.1
                              have p39_3 := h39c.2.2.2
                              linarith only [hlam, p39_0]
                        · linarith only [h11, h4, hc23, hlam, hphi, u3elo0]
                      · linarith only [h10, h3, h5, hlam, hphi, ht12, ht23, u1ehi3, u3elo0]
                    · linarith only [h9, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
                  · linarith only [h8, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h69 | h69
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h70 | h70
                    · linarith only [h6, h7, h70, hlam]
                    · linarith only [h69, h70, hlam, hphi, ht12, ht23, u1ehi3, u3elo4]
                  · linarith only [h69, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
              · linarith only [h6, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
              · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
                · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
                      · linarith only [h2, h5, h77, h79, hlam, hphi, ht12, ht23, u1ehi4, u3elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h81 | h81
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h82 | h82
                          · linarith only [h79, h82, hc24, hlam, hphi, ht12, u1ehi3]
                          · rcases h5bigk with h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [hlam, p84_0]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h79, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p84_1, u1ehi3]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h4, h82, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p84_1, u3elo0]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p84_1, u3elo0]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h5, hlam, p84_1]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h2, hlam, p84_0]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [hlam, p84_0]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h2, h82, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p84_1]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h2, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p84_1, u3elo0]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h79, hlam, p84_1]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h2, hc25, hlam, hphi, ht12, p84_1, u1ehi4]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h76, hlam, p84_1]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [hlam, p84_0]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h75, h81, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p84_1]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h82, hlam, p84_1]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h4, hlam, p84_0]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h78, hlam, p84_0]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h81, hlam, p84_0]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [hlam, p84_0]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h79, hlam, hphi, ht12, ht23, p84_1, u1ehi3, u3elo4]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h2, h79, hc45, hlam, hphi, ht12, ht23, ht34, p84_1, u1ehi3]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h79, hc45, hlam, hphi, ht12, ht23, ht34, p84_1, u1ehi3]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [h82, hc24, hc45, hlam, hphi, p84_1]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              rcases p84_3 (m.d 0 5) (by simp) with h108 | h108
                              · linarith only [h108, h5, hlam]
                              · linarith only [h108, h4, hlam]
                            · have p84_0 := h84c.1
                              have p84_1 := h84c.2.1
                              have p84_2 := h84c.2.2.1
                              have p84_3 := h84c.2.2.2
                              linarith only [hlam, p84_0]
                        · linarith only [h4, h81, hc23, hlam, hphi, u3elo0]
                    · linarith only [h4, h78, hc13, hlam, hphi, u3elo0]
                  · linarith only [h77, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                    · linarith only [h116, h75, h76, hlam]
                    · linarith only [h115, h116, hlam, hphi, ht12, ht23, u1ehi3, u3elo4]
                  · linarith only [h115, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
              · linarith only [h75, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
          · linarith only [h1, h4, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
        · linarith only [h1, h3, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
      · linarith only [h0, h2, hc15, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h125 | h125
    · linarith only [h0, h125, hc12, hlam, hphi, u1ehi2]
    · linarith only [h125, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_11_13_25_L_R_L_0_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3elo := hb3.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
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
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · rcases h5bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc15, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc25, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc35, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc45, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h11, h9, hc45, hlam, hphi, p12_1, u5elo1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, h11, hc45, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, hc45, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, hc25, hlam, hphi, ht12, p12_1, u1ehi4]
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
                            linarith only [h1, h11, h4, hc45, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, h4, hc45, hlam, hphi, p12_1, u5elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h2, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h6, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h9, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc45, hlam, hphi, p12_1, u5elo3]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h11, h3, h8, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12_1, u3elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h7, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h10, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h11, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                        · rcases h5bigk with h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [hlam, p38_0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p38_1, u1ehi4, u5elo0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h10, h11, hc34, hlam, hphi, ht45, p38_1, u5elo0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [hc35, hlam, hphi, p38_1, u5elo0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h11, hc34, hlam, hphi, ht45, p38_1, u5elo0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h1, hlam, p38_0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [hlam, p38_0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h10, h11, hc34, hlam, hphi, ht45, p38_1, u5elo1]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h1, h11, hc34, hlam, hphi, ht45, p38_1, u5elo0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h1, h11, hc34, hlam, hphi, ht45, p38_1, u5elo0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h1, hc25, hlam, hphi, ht12, p38_1, u1ehi4]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h4, hlam, p38_1]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [hlam, p38_0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h1, h11, h4, hc34, hlam, hphi, ht45, p38_1, u5elo0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h1, h11, h4, hc34, hlam, hphi, ht45, p38_1, u5elo0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h2, hlam, p38_0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h6, hlam, p38_0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h9, hlam, p38_0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [hlam, p38_0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h11, hlam, p38_1]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h0, h10, h3, h8, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p38_1, u3elo0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h7, hlam, p38_0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h10, hlam, p38_0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [h0, h10, h11, h3, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p38_1, u3elo0]
                          · have p38_0 := h38c.1
                            have p38_1 := h38c.2.1
                            have p38_2 := h38c.2.2.1
                            have p38_3 := h38c.2.2.2
                            linarith only [hlam, p38_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                        · linarith only [h0, h10, h5, h64, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · rcases h5bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [hlam, p66_0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p66_1, u1ehi4, u5elo0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [hc25, hlam, hphi, p66_1, u5elo0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h64, hc34, hlam, hphi, ht45, p66_1, u5elo0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h10, h8, hc34, hlam, hphi, ht45, p66_1, u5elo0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h1, hlam, p66_0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [hlam, p66_0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h64, h9, hc34, hlam, hphi, ht45, p66_1, u5elo1]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h1, h64, hc34, hlam, hphi, ht45, p66_1, u5elo0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h1, h10, h8, hc34, hlam, hphi, ht45, p66_1, u5elo0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h1, hc25, hlam, hphi, ht12, p66_1, u1ehi4]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h4, hlam, p66_1]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [hlam, p66_0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h1, h4, h64, hc34, hlam, hphi, ht45, p66_1, u5elo0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h10, hlam, p66_1]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h2, hlam, p66_0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h6, hlam, p66_0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h9, hlam, p66_0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [hlam, p66_0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h64, hlam, p66_1]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h0, h5, h7, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p66_1, u3elo0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h7, hlam, p66_0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h0, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p66_1, u3elo0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [h0, h5, h64, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u3elo0]
                          · have p66_0 := h66c.1
                            have p66_1 := h66c.2.1
                            have p66_2 := h66c.2.2.1
                            have p66_3 := h66c.2.2.2
                            linarith only [hlam, p66_0]
                    · linarith only [h2, h9, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h5, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
              · linarith only [h6, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
            · linarith only [h5, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
          · linarith only [h4, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo2]
        · linarith only [h3, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
      · linarith only [h0, h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
    · linarith only [h1, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
  · linarith only [h0, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_11_13_25_L_R_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h4, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h0, h10, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
                · linarith only [h14, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h16 | h16
                  · linarith only [h1, h16, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h13, h14, h18, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                      · linarith only [h0, h13, h14, h20, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h20, h5, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                · linarith only [h13, h23, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h1, h25, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h27 | h27
                    · linarith only [h2, h27, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                        · linarith only [h25, h30, hc23, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h29, h30, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h29, h5, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
            · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
              · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                · linarith only [h0, h36, h4, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h38 | h38
                  · linarith only [h1, h38, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                    · linarith only [h2, h40, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                      · linarith only [h0, h34, h4, h42, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h44 | h44
                        · linarith only [h0, h35, h38, h4, h42, h44, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h0, h35, h4, h42, h44, hc35, hlam, hphi, u3ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h47 | h47
                · linarith only [h0, h4, h47, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                  · linarith only [h1, h49, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                    · linarith only [h2, h51, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h34, h35, h51, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
              · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h4, h55, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h57 | h57
                  · linarith only [h1, h57, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                    · linarith only [h2, h59, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                      · linarith only [h34, h54, h57, h61, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h34, h61, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
                · linarith only [h34, h4, h64, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h66 | h66
                  · linarith only [h1, h66, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                    · linarith only [h2, h68, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                        · linarith only [h66, h71, hc23, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h70, h71, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h34, h70, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h78 | h78
    · linarith only [h0, h78, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h80 | h80
      · linarith only [h0, h80, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h82 | h82
        · linarith only [h0, h82, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h84 | h84
          · rcases m.htr 1 2 3 (by decide) (by decide) with h85 | h85
            · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
              · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
                · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h91 | h91
                        · linarith only [h85, h91, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h90, h91, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                        · linarith only [h90, h94, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                          · linarith only [h86, h96, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                            · linarith only [h90, h96, h98, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h86, h89, h90, h98, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h80, h89, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                  · linarith only [h78, h88, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                · linarith only [h0, h84, h87, hlam]
              · linarith only [h0, h84, h86, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · linarith only [h0, h84, h85, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
            · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
              · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                · linarith only [h0, h108, h84, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h108, hc25, hlam, hphi, ht12, u1ehi0]
              · linarith only [h106, h107, h78, hc24, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h106, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
