import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_M_LR_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                    · linarith only [h0, h3, h9, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h3, h5, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                · linarith only [h2, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h1, h5, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
            · linarith only [h0, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
            · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                    · linarith only [h0, h20, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                    · linarith only [h0, h20, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                  · linarith only [h0, h16, h19, h3, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                · linarith only [h16, h18, hc25, hlam, hphi, u2ehi2]
              · linarith only [h16, h17, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h16, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
          · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
            · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                  · linarith only [h3, h31, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                    · linarith only [h0, h3, h33, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                      · linarith only [h1, h35, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · linarith only [h27, h35, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                · linarith only [h2, h29, h30, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi3]
              · linarith only [h28, h29, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h28, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
            · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
              · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                  · linarith only [h3, h44, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                    · linarith only [h0, h46, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h48 | h48
                      · linarith only [h1, h27, h48, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h50 | h50
                        · linarith only [h27, h3, h50, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                        · linarith only [h2, h3, h46, h48, h50, hc45, hlam, hphi, ht23, ht34, u0ehi7, u0elo1, u2ehi2]
                · linarith only [h2, h43, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
              · linarith only [h41, h42, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h41, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
      · linarith only [h0, h2, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h58 | h58
    · linarith only [h0, h58, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h60 | h60
      · linarith only [h0, h60, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h62 | h62
        · rcases m.htr 0 4 5 (by decide) (by decide) with h63 | h63
          · rcases m.htr 1 2 3 (by decide) (by decide) with h64 | h64
            · linarith only [h0, h64, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
              · linarith only [h58, h66, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
                · linarith only [h60, h68, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h70 | h70
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h73 | h73
                        · linarith only [h62, h73, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                        · linarith only [h63, h73, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                      · linarith only [h62, h63, h72, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
                    · linarith only [h0, h71, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h62, h64, h70, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
            · linarith only [h0, h79, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
              · linarith only [h58, h81, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                · linarith only [h60, h83, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h85 | h85
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                      · linarith only [h63, h86, h87, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                      · linarith only [h81, h87, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                    · linarith only [h62, h86, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
                  · linarith only [h62, h79, h85, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h92 | h92
          · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
            · linarith only [h0, h93, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
              · linarith only [h58, h95, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                · linarith only [h60, h97, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                  · linarith only [h0, h62, h93, h99, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                    · linarith only [h101, h93, h99, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h0, h101, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
            · linarith only [h0, h104, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
              · linarith only [h104, h106, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                · linarith only [h104, h108, h60, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                  · linarith only [h0, h110, h62, hc13, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                    · linarith only [h104, h110, h112, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h0, h112, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]

theorem r1l7_20_12_15_M_IR_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc12 := m.hcor 1 2 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases h0bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h0, h10, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h6, h8, hc01, hlam, hphi, p11_1, u0ehi4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h8, hc01, hlam, hphi, p11_1, u0ehi4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hc01, hlam, hphi, p11_1, u0ehi4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h0, hlam, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h6, h8, hc02, hlam, hphi, p11_1, u0ehi4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h8, hlam, hphi, ht01, ht12, p11_1, u0ehi4, u2elo0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, hphi, ht01, ht12, p11_1, u0ehi4, u2elo0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hc03, hlam, hphi, p11_1, u0ehi0]
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
                          linarith only [h3, h8, hlam, hphi, ht01, ht12, p11_1, u0ehi4, u2elo0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h3, hlam, hphi, ht01, ht12, p11_1, u0ehi4, u2elo0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h1, hlam, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h4, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h6, hlam, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hc04, hlam, hphi, p11_1, u0ehi4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h2, hlam, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h5, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h7, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h8, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                      · rcases h0bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h10, h3, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p37_1]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h10, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p37_1]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h10, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p37_1]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hc01, hlam, hphi, p37_1, u0ehi4]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h0, hlam, p37_1]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h10, h6, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p37_1, u2elo0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h10, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p37_1, u2elo0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, hphi, ht01, ht12, p37_1, u0ehi4, u2elo0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hc03, hlam, hphi, p37_1, u0ehi0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h3, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h10, h8, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p37_1]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h3, hlam, hphi, ht01, ht12, p37_1, u0ehi4, u2elo0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h1, hlam, p37_1]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h4, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h6, hlam, p37_1]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h3, h6, hlam, hphi, ht01, ht12, p37_1, u0ehi4, u2elo0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h2, hlam, p37_1]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h5, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h7, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h8, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                    · linarith only [h4, h9, hc12, hlam, hphi, u2elo0]
                  · linarith only [h8, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
                · linarith only [h6, h7, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h66 | h66
                · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h68 | h68
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                      · rcases h0bigk with h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hc01, hlam, hphi, p70_1, u0ehi1]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hc01, hlam, hphi, p70_1, u0ehi2]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h6, hc01, hlam, hphi, p70_1, u0ehi2]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hc01, hlam, hphi, p70_1, u0ehi4]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h0, hlam, p70_1]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hc02, hlam, hphi, p70_1, u0ehi2]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h6, hlam, hphi, ht01, ht12, p70_1, u0ehi2, u2elo0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hlam, hphi, ht01, ht12, p70_1, u0ehi4, u2elo0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h6, hc01, hc34, hlam, hphi, ht12, ht23, p70_1]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h3, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h6, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h4, h6, hlam, hphi, ht01, ht12, p70_1, u0ehi4, u2elo0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h1, hlam, p70_1]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h4, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h4, h66, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p70_1, u2elo0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h4, hlam, hphi, ht01, ht12, p70_1, u0ehi4, u2elo0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h2, hlam, p70_1]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h5, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h66, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [h67, hlam, p70_0]
                        · have p70_0 := h70c.1
                          have p70_1 := h70c.2.1
                          have p70_2 := h70c.2.2.1
                          have p70_3 := h70c.2.2.2
                          linarith only [hlam, p70_0]
                      · rcases h0bigk with h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c | h96c
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h4, h67, h69, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h66, hc01, hlam, hphi, p96_1, u0ehi4]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h67, h69, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hc01, hlam, hphi, p96_1, u0ehi4]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h0, hlam, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h66, hc02, hlam, hphi, p96_1, u0ehi4]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h67, h69, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hlam, hphi, ht01, ht12, p96_1, u0ehi4, u2elo0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hc03, hlam, hphi, p96_1, u0ehi0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h3, hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h6, hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hc03, hlam, hphi, p96_1, u0ehi4]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h1, hlam, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h4, hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hc04, hlam, hphi, p96_1, u0ehi2]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h4, hlam, hphi, ht01, ht12, p96_1, u0ehi4, u2elo0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h2, hlam, p96_1]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h5, hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h66, hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [h67, hlam, p96_0]
                        · have p96_0 := h96c.1
                          have p96_1 := h96c.2.1
                          have p96_2 := h96c.2.2.1
                          have p96_3 := h96c.2.2.2
                          linarith only [hlam, p96_0]
                    · linarith only [h4, h68, hc12, hlam, hphi, u2elo0]
                  · linarith only [h67, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi3, u5elo4]
                · linarith only [h66, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo3]
            · linarith only [h5, hlam, hphi, ht01, ht12, u0ehi1, u2elo4]
          · linarith only [h3, h4, hlam, hphi, ht01, ht12, u0ehi2, u2elo3]
        · linarith only [h3, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h129 | h129
      · rcases m.htr 0 2 3 (by decide) (by decide) with h130 | h130
        · rcases m.htr 0 2 4 (by decide) (by decide) with h131 | h131
          · linarith only [h0, h1, h131, hlam]
          · linarith only [h130, h131, hlam, hphi, ht01, ht12, u0ehi2, u2elo3]
        · linarith only [h130, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
      · linarith only [h0, h129, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi1, u5elo1]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

theorem r1l7_20_12_H_L_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
      · linarith only [h2, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
        · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h13, h6, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h13, h6, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h12, h4, h6, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                  · linarith only [h10, h11, h4, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h10, h2, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h6, h9, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
              · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                      · linarith only [h24, h6, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h24, h6, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h23, h4, h6, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
                  · linarith only [h0, h22, h8, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h21, h8, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h20, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
            · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
              · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h35, h4, h7, hc24, hlam, hphi, u2ehi0]
                    · linarith only [h35, h4, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h2, h34, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h2, h33, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
              · linarith only [h2, h31, h32, h6, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
              · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                    · linarith only [h4, h44, h7, hc24, hlam, hphi, u2ehi0]
                    · linarith only [h4, h44, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                  · linarith only [h0, h31, h43, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h31, h42, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h41, h6, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h50 | h50
          · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
            · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
              · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                · linarith only [h2, h53, h6, hc23, hlam, hphi, u2ehi0]
                · linarith only [h2, h51, h52, h53, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · linarith only [h2, h51, h52, hc34, hlam, hphi, ht23, u2ehi0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
              · linarith only [h2, h51, h57, h6, hc23, hlam, hphi, u2ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                · linarith only [h2, h59, h6, hc23, hlam, hphi, u2ehi0]
                · linarith only [h2, h59, hc34, hlam, hphi, ht23, u2ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
            · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
              · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                · linarith only [h2, h6, h64, hc23, hlam, hphi, u2ehi0]
                · linarith only [h2, h62, h63, h64, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · linarith only [h2, h62, h63, hc34, hlam, hphi, ht23, u2ehi0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h68 | h68
              · linarith only [h2, h6, h62, h68, hc23, hlam, hphi, u2ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                · linarith only [h0, h62, h68, h70, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h2, h70, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_20_13_14_M_IR_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h6, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h3, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h4, h7, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h13, h14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                    · linarith only [h14, h3, h5, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi3]
                  · linarith only [h13, h3, hc23, hlam, hphi, u3elo0]
                · linarith only [h12, h4, h6, hc12, hlam, hphi, ht23, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                  · linarith only [h0, h19, h21, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h21, h3, hc23, hlam, hphi, u3elo0]
                · linarith only [h19, h20, h4, hc23, hlam, hphi, u3elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                    · linarith only [h26, h27, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases h0bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hc01, hlam, hphi, p29_1, u0ehi1]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hc01, hlam, hphi, p29_1, u0ehi2]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hc01, hlam, hphi, p29_1, u0ehi3]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h5, hc01, hlam, hphi, p29_1, u0ehi3]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h0, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h19, h2, h25, h27, hc02, hlam, hphi, ht0b, ht45, ht5b, p29_1, u4ehi3]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, p29_1, u0ehi3]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h0, h5, hc01, hlam, hphi, p29_1, u0ehi3]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h1, hlam, p29_1]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h2, hlam, p29_1]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hc03, hlam, hphi, p29_1, u0ehi3]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h5, hlam, hphi, ht01, ht12, ht23, p29_1, u0ehi3, u3elo0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h5, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p29_1]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h19, h2, h25, h27, h5, hc45, hlam, hphi, p29_1, u4ehi3]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h3, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h5, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h0, h19, h2, h25, h27, hc05, hlam, hphi, ht0b, ht45, ht5b, p29_1, u4ehi3]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h19, h2, h25, h27, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p29_1, u3elo0, u4ehi3]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h4, hlam, p29_0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p29_1, u3elo0, u4ehi0]
                      · have p29_0 := h29c.1
                        have p29_1 := h29c.2.1
                        have p29_2 := h29c.2.2.1
                        have p29_3 := h29c.2.2.2
                        linarith only [hlam, p29_0]
                  · linarith only [h19, h26, h3, hc13, hlam, hphi, u3elo0]
                · linarith only [h19, h25, h4, hc12, hlam, hphi, ht23, u3elo0]
          · linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h61 | h61
    · rcases m.htr 0 2 3 (by decide) (by decide) with h62 | h62
      · rcases m.htr 0 3 4 (by decide) (by decide) with h63 | h63
        · rcases m.htr 0 3 5 (by decide) (by decide) with h64 | h64
          · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
            · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
              · rcases m.htr 1 3 5 (by decide) (by decide) with h67 | h67
                · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                  · linarith only [h0, h61, h66, h68, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h63, h68, hc23, hlam, hphi, u3elo0]
                · linarith only [h64, h67, hc13, hlam, hphi, u3elo0]
              · linarith only [h0, h66, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
              · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                  · linarith only [h0, h61, h73, h75, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h63, h75, hc23, hlam, hphi, u3elo0]
                · linarith only [h64, h74, hc13, hlam, hphi, u3elo0]
              · linarith only [h0, h73, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h63, h64, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
        · linarith only [h63, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · linarith only [h0, h61, h62, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo2]
    · linarith only [h61, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_20_13_15_H_L_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · linarith only [h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
          · linarith only [h0, h1, h4, h5, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8 | h8
          · linarith only [h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
          · linarith only [h1, h3, h8, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h11 | h11
        · linarith only [h0, h11, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h13 | h13
          · linarith only [h13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h15 | h15
            · linarith only [h13, h15, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h17 | h17
              · linarith only [h17, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
                · linarith only [h0, h1, h13, h17, h19, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                  · linarith only [h0, h1, h11, h13, h17, h21, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                    · linarith only [h0, h1, h13, h17, h21, h23, hc12, hc24, hlam, hphi]
                    · linarith only [h0, h23, h3, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h26 | h26
    · linarith only [h26, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h28 | h28
      · rcases m.htr 0 2 4 (by decide) (by decide) with h29 | h29
        · rcases m.htr 0 3 4 (by decide) (by decide) with h30 | h30
          · linarith only [h30, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
          · linarith only [h26, h28, h30, hlam]
        · linarith only [h0, h28, h29, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h34 | h34
        · rcases m.htr 0 3 4 (by decide) (by decide) with h35 | h35
          · linarith only [h35, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h37 | h37
            · linarith only [h34, h35, h37, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h39 | h39
              · linarith only [h34, h39, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
                · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h43 | h43
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                      · linarith only [h26, h35, h41, h44, hc01, hc12, hlam, hphi]
                      · linarith only [h34, h44, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                      · linarith only [h35, h41, h47, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h34, h47, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                  · linarith only [h34, h42, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                    · linarith only [h28, h39, h41, h51, h52, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                      · linarith only [h34, h35, h54, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                      · linarith only [h0, h41, h54, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h34, h51, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
          · linarith only [h58, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h60 | h60
            · linarith only [h60, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h62 | h62
              · linarith only [h62, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h64 | h64
                · rcases m.htr 1 2 4 (by decide) (by decide) with h65 | h65
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                      · linarith only [h58, h64, h67, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h69 | h69
                        · linarith only [h60, h67, h69, hc34, hlam, hphi, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                          · linarith only [h58, h62, h65, h71, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h0, h34, h66, h71, hc01, hc14, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                      · linarith only [h58, h64, h74, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h76 | h76
                        · linarith only [h60, h64, h76, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                          · linarith only [h65, h66, h78, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h80 | h80
                            · linarith only [h65, h66, h74, h80, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h58, h80, hc45, hlam, hphi, ht34, u3ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h83 | h83
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                      · linarith only [h58, h64, h65, h84, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h64, h65, h84, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h64, h65, h83, hc45, hlam, hphi, ht34, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                  · linarith only [h0, h34, h64, h88, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h93 | h93
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h94 | h94
                            · linarith only [h58, h62, h91, h94, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h58, h90, h94, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h88, h90, h93, hlam]
                        · linarith only [h0, h88, h91, h92, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h58, h62, h64, h88, h90, h91, hc01, hc24, hc34, hlam, hphi, ht12, u3ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h100 | h100
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h101 | h101
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h102 | h102
                          · linarith only [h0, h100, h102, h88, h90, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h102, h88, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h100, h101, h58, hc35, hlam, hphi, u3ehi0]
                      · linarith only [h0, h100, h64, hc01, hc34, hlam, hphi, ht12, ht23]

theorem r1l7_20_13_15_M_IR_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
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
                      linarith only [h0, h5, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p9_1]
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
                      linarith only [hc02, hlam, hphi, p9_1, u0ehi0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h0, h5, h8, hc02, hc45, hlam, hphi, ht0b, ht5b, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc02, hlam, hphi, p9_1, u0ehi3]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc02, hlam, hphi, p9_1, u0ehi4]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h0, hlam, p9_1]
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
                      linarith only [hlam, hphi, ht01, ht12, ht23, p9_1, u0ehi3, u3elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, hphi, ht01, ht12, ht23, p9_1, u0ehi4, u3elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h1, hlam, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc04, hlam, hphi, p9_1, u0ehi1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h3, hlam, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h3, hlam, hphi, ht01, ht12, ht23, p9_1, u0ehi4, u3elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h2, hlam, p9_1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc05, hlam, hphi, p9_1, u0ehi1]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [h4, hlam, p9_0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hc04, hlam, hphi, ht45, p9_1, u5elo0]
                    · have p9_0 := h9c.1
                      have p9_1 := h9c.2.1
                      have p9_2 := h9c.2.2.1
                      have p9_3 := h9c.2.2.2
                      linarith only [hlam, p9_0]
                  · rcases h0bigk with h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c | h35c
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, p35_0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc01, hlam, hphi, p35_1, u0ehi1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc01, hlam, hphi, p35_1, u0ehi2]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc01, hlam, hphi, p35_1, u0ehi3]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc01, hlam, hphi, p35_1, u0ehi4]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc02, hlam, hphi, p35_1, u0ehi0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, p35_0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h0, h5, h7, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p35_1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h1, h7, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p35_1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc02, hlam, hphi, p35_1, u0ehi4]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h0, hlam, p35_1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc02, hlam, hphi, ht23, p35_1, u3elo0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, p35_0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h1, h7, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p35_1, u3elo0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, hphi, ht01, ht12, ht23, p35_1, u0ehi4, u3elo0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h1, hlam, p35_1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc04, hlam, hphi, p35_1, u0ehi1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h3, hlam, p35_1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, p35_0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h3, hlam, hphi, ht01, ht12, ht23, p35_1, u0ehi4, u3elo0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h2, hlam, p35_1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc05, hlam, hphi, p35_1, u0ehi1]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [h4, hlam, p35_0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hc04, hlam, hphi, ht45, p35_1, u5elo0]
                    · have p35_0 := h35c.1
                      have p35_1 := h35c.2.1
                      have p35_2 := h35c.2.2.1
                      have p35_3 := h35c.2.2.2
                      linarith only [hlam, p35_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h61 | h61
                  · linarith only [h3, h61, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · rcases h0bigk with h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc01, hlam, hphi, p63_1, u0ehi1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc01, hlam, hphi, p63_1, u0ehi2]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc01, hlam, hphi, p63_1, u0ehi3]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc01, hlam, hphi, p63_1, u0ehi4]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc02, hlam, hphi, p63_1, u0ehi0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h3, hc02, hlam, hphi, p63_1, u0ehi3]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc02, hlam, hphi, p63_1, u0ehi3]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc02, hlam, hphi, p63_1, u0ehi4]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h0, hlam, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc03, hlam, hphi, p63_1, u0ehi1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, hphi, ht01, ht12, ht23, p63_1, u0ehi3, u3elo0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, hphi, ht01, ht12, ht23, p63_1, u0ehi4, u3elo0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h1, hlam, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc04, hlam, hphi, p63_1, u0ehi1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h3, hlam, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h3, hlam, hphi, ht01, ht12, ht23, p63_1, u0ehi4, u3elo0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h2, hlam, p63_1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc05, hlam, hphi, p63_1, u0ehi1]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [h4, hlam, p63_0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hc04, hlam, hphi, ht45, p63_1, u5elo0]
                    · have p63_0 := h63c.1
                      have p63_1 := h63c.2.1
                      have p63_2 := h63c.2.2.1
                      have p63_3 := h63c.2.2.2
                      linarith only [hlam, p63_0]
              · linarith only [h4, h6, hc13, hlam, hphi, u3elo0]
            · linarith only [h3, h5, hc13, hlam, hphi, u3elo0]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi0, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h94 | h94
      · rcases m.htr 0 3 4 (by decide) (by decide) with h95 | h95
        · linarith only [h0, h1, h95, hlam]
        · linarith only [h95, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · linarith only [h0, h94, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi2, u5elo1]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

theorem r1l7_21_14_H_R_L_I (m : N7Model)
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h11, h13, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h11, h12, h13, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                            · linarith only [h0, h12, h16, h7, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases h4bigk with h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h0, h10, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p18_1, u1ehi4]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                rcases p18_3 (m.d 0 4) (by simp) with h21 | h21
                                · rcases p18_3 (m.d 1 4) (by simp) with h22 | h22
                                  · linarith only [h2, h22, hlam]
                                  · linarith only [h22, h8, hlam]
                                · linarith only [h21, h4, hlam]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                rcases p18_3 (m.d 0 4) (by simp) with h26 | h26
                                · rcases p18_3 (m.d 1 4) (by simp) with h27 | h27
                                  · linarith only [h2, h27, hlam]
                                  · linarith only [h27, h9, hlam]
                                · linarith only [h26, h5, hlam]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                rcases p18_3 (m.d 0 4) (by simp) with h31 | h31
                                · rcases p18_3 (m.d 1 4) (by simp) with h32 | h32
                                  · linarith only [h2, h32, hlam]
                                  · linarith only [h10, h32, hlam]
                                · linarith only [h31, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h2, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                rcases p18_3 (m.d 0 4) (by simp) with h38 | h38
                                · rcases p18_3 (m.d 1 4) (by simp) with h39 | h39
                                  · rcases p18_3 (m.d 2 4) (by simp) with h40 | h40
                                    · linarith only [h40, h8, hlam]
                                    · rcases p18_3 (m.d 3 4) (by simp) with h42 | h42
                                      · linarith only [h42, h9, hlam]
                                      · rcases p18_3 (m.d 4 5) (by simp) with h44 | h44
                                        · linarith only [h10, h44, hlam]
                                        · linarith only [h12, h44, hlam]
                                  · linarith only [h39, h8, hlam]
                                · linarith only [h38, h4, hlam]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                rcases p18_3 (m.d 0 4) (by simp) with h49 | h49
                                · rcases p18_3 (m.d 1 4) (by simp) with h50 | h50
                                  · rcases p18_3 (m.d 2 4) (by simp) with h51 | h51
                                    · linarith only [h51, h8, hlam]
                                    · linarith only [h11, h51, hlam]
                                  · linarith only [h50, h9, hlam]
                                · linarith only [h49, h5, hlam]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h0, h11, h12, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h4, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h8, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h12, hc34, hc45, hlam, hphi, p18_1]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h12, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h5, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h9, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h11, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h16, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h6, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h10, hlam, p18_0]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h0, h10, h7, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [h0, h10, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p18_1]
                              · have p18_0 := h18c.1
                                have p18_1 := h18c.2.1
                                have p18_2 := h18c.2.2.1
                                have p18_3 := h18c.2.2.2
                                linarith only [hlam, p18_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h73 | h73
                            · rcases h4bigk with h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h0, h10, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p74_1, u1ehi4]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                rcases p74_3 (m.d 0 4) (by simp) with h77 | h77
                                · rcases p74_3 (m.d 1 4) (by simp) with h78 | h78
                                  · linarith only [h2, h78, hlam]
                                  · linarith only [h78, h8, hlam]
                                · linarith only [h4, h77, hlam]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                rcases p74_3 (m.d 0 4) (by simp) with h82 | h82
                                · rcases p74_3 (m.d 1 4) (by simp) with h83 | h83
                                  · linarith only [h2, h83, hlam]
                                  · linarith only [h83, h9, hlam]
                                · linarith only [h5, h82, hlam]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                rcases p74_3 (m.d 0 4) (by simp) with h87 | h87
                                · rcases p74_3 (m.d 1 4) (by simp) with h88 | h88
                                  · linarith only [h2, h88, hlam]
                                  · linarith only [h10, h88, hlam]
                                · linarith only [h87, hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h2, hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h2, h72, hc01, hc45, hlam, hphi, ht0b, ht5b, p74_1]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h0, h11, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p74_1]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                rcases p74_3 (m.d 0 4) (by simp) with h96 | h96
                                · rcases p74_3 (m.d 1 4) (by simp) with h97 | h97
                                  · rcases p74_3 (m.d 2 4) (by simp) with h98 | h98
                                    · linarith only [h8, h98, hlam]
                                    · linarith only [h72, h98, hlam]
                                  · linarith only [h97, hlam, p74_0]
                                · linarith only [h6, h96, hlam]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h4, hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h8, hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h11, hlam, p74_1]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h0, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p74_1]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h5, hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h9, hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h0, h7, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p74_1]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h0, h7, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p74_1]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h6, hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h10, hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h72, hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [h73, hlam, p74_0]
                              · have p74_0 := h74c.1
                                have p74_1 := h74c.2.1
                                have p74_2 := h74c.2.2.1
                                have p74_3 := h74c.2.2.2
                                linarith only [hlam, p74_0]
                            · linarith only [h0, h72, h73, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h119 | h119
                            · linarith only [h0, h119, h7, h72, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h10, h11, h119, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h10, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
                    · linarith only [h9, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                  · linarith only [h8, hc24, hlam, hphi, ht12, u1ehi1]
                · linarith only [h7, hc23, hlam, hphi, ht12, u1ehi1]
              · linarith only [h2, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
            · linarith only [h1, h5, hc34, hlam, hphi, ht12, ht23, u1ehi2]
          · linarith only [h0, h4, hc24, hlam, hphi, ht12, u1ehi1]
        · linarith only [h3, hc15, hlam, hphi, u1ehi0]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem r1l7_22_13_15_H_L_L_0_L_I (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                            · linarith only [h0, h12, h14, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · linarith only [h14, h6, hc23, hlam, hphi, u3elo0]
                        · linarith only [h11, h4, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · linarith only [h10, hc12, hlam, hphi, u2elo4]
                    · linarith only [h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h8, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                        · linarith only [h2, h24, h7, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                          · linarith only [h21, h26, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                            · linarith only [h0, h22, h26, h28, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · linarith only [h28, h6, hc23, hlam, hphi, u3elo0]
                      · linarith only [h23, hc12, hlam, hphi, u2elo4]
                    · linarith only [h21, h22, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h21, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
                · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                          · linarith only [h35, h39, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
                            · linarith only [h0, h36, h39, h41, h6, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
                              · linarith only [h0, h36, h43, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h34, h39, h4, h43, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · linarith only [h34, h38, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · linarith only [h37, hc12, hlam, hphi, u2elo4]
                    · linarith only [h35, h36, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h35, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
                        · linarith only [h2, h34, h53, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                          · linarith only [h50, h55, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                            · linarith only [h3, h4, h55, h57, h6, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h59 | h59
                              · linarith only [h2, h34, h51, h59, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h61 | h61
                                · linarith only [h2, h34, h51, h55, h61, hc23, hlam, hphi, u3elo3]
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
                                    linarith only [h5, h51, h53, h55, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p63_1, u2elo0]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h5, h55, h59, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p63_1, u2elo0]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h6, hlam, p63_0]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h34, hlam, p63_0]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h3, hlam, p63_0]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [hlam, p63_0]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h3, h5, h55, h59, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p63_1, u2elo0]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h52, h6, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p63_1, u2elo1]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h53, hlam, p63_0]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h5, hlam, p63_1]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h52, hlam, p63_1]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [hlam, p63_0]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h57, hlam, p63_1]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h59, hlam, p63_0]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h5, h55, h59, hc23, hlam, hphi, p63_1, u3elo4]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h52, h55, h59, hc23, hlam, hphi, p63_1, u3elo4]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h55, h59, hc23, hlam, hphi, p63_1, u3elo4]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [hlam, p63_0]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h61, hlam, p63_0]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    rcases p63_3 (m.d 0 5) (by simp) with h84 | h84
                                    · linarith only [h34, h84, hlam]
                                    · rcases p63_3 (m.d 1 5) (by simp) with h86 | h86
                                      · linarith only [h53, h86, hlam]
                                      · rcases p63_3 (m.d 2 5) (by simp) with h88 | h88
                                        · linarith only [h59, h88, hlam]
                                        · rcases p63_3 (m.d 3 5) (by simp) with h90 | h90
                                          · linarith only [h61, h90, hlam]
                                          · linarith only [h6, h90, hlam]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    rcases p63_3 (m.d 0 5) (by simp) with h93 | h93
                                    · linarith only [h34, h93, hlam]
                                    · linarith only [h3, h93, hlam]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    rcases p63_3 (m.d 0 5) (by simp) with h96 | h96
                                    · linarith only [h34, h96, hlam]
                                    · linarith only [h5, h96, hlam]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [h1, h50, h6, hc23, hc45, hlam, hphi, ht34, p63_1]
                                  · have p63_0 := h63c.1
                                    have p63_1 := h63c.2.1
                                    have p63_2 := h63c.2.2.1
                                    have p63_3 := h63c.2.2.2
                                    linarith only [hlam, p63_0]
                      · linarith only [h52, hc12, hlam, hphi, u2elo4]
                    · linarith only [h50, h51, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h50, hc12, hlam, hphi, u2elo2]
            · linarith only [h5, hc02, hlam, hphi, u2elo4]
          · linarith only [h0, h4, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h106 | h106
          · rcases m.htr 0 2 5 (by decide) (by decide) with h107 | h107
            · linarith only [h0, h107, h3, hc12, hlam, hphi, u2elo0]
            · linarith only [h107, hc02, hlam, hphi, u2elo4]
          · linarith only [h0, h106, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h111 | h111
        · rcases m.htr 0 2 4 (by decide) (by decide) with h112 | h112
          · linarith only [h0, h112, h2, hc12, hlam, hphi, u2elo0]
          · linarith only [h112, hc02, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h115 | h115
          · linarith only [h0, h115, h2, hc12, hlam, hphi, u2elo0]
          · linarith only [h115, hc02, hlam, hphi, u2elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · linarith only [h0, hc01, hlam, hphi, ht12, u2elo1]

end R2N4
