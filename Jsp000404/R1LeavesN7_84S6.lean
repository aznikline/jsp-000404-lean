import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_M_LR_L_0_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h5, h6, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                · linarith only [h3, h6, h8, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h10, h5, h8, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, h2, h3, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
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
                        rcases p14_3 (m.d 0 3) (by simp) with h16 | h16
                        · rcases p14_3 (m.d 1 3) (by simp) with h17 | h17
                          · linarith only [h1, h17, hlam]
                          · rcases p14_3 (m.d 2 3) (by simp) with h19 | h19
                            · linarith only [h19, h2, hlam]
                            · rcases p14_3 (m.d 3 4) (by simp) with h21 | h21
                              · linarith only [h21, h3, hlam]
                              · linarith only [h21, h6, hlam]
                        · linarith only [h1, h16, hlam]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        rcases p14_3 (m.d 0 3) (by simp) with h25 | h25
                        · rcases p14_3 (m.d 1 3) (by simp) with h26 | h26
                          · linarith only [h1, h26, hlam]
                          · linarith only [h26, h5, hlam]
                        · linarith only [h2, h25, hlam]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h0, h2, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14_1, u1elo0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h0, h2, h5, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14_1, u1elo0]
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
                        linarith only [h6, hc23, hc34, hlam, hphi, p14_1]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h6, hlam, p14_0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h8, hlam, p14_0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h2, hlam, p14_0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h5, hlam, p14_0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [hlam, p14_0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h5, h6, hlam, p14_1]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h10, hlam, p14_0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h3, hlam, p14_0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h0, h2, h3, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14_1, u1elo0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h0, h12, h2, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14_1, u1elo0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [hlam, p14_0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h12, hlam, p14_1]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h4, hlam, p14_0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h0, h2, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14_1, u1elo0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h0, h2, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14_1, u1elo0]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [h0, h2, h4, h6, hlam, hphi, ht01, ht0b, ht45, ht5b, p14_1, u1elo0, u4ehi1]
                      · have p14_0 := h14c.1
                        have p14_1 := h14c.2.1
                        have p14_2 := h14c.2.2.1
                        have p14_3 := h14c.2.2.2
                        linarith only [hlam, p14_0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
              · linarith only [h1, h52, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h54 | h54
                · linarith only [h0, h2, h3, h52, h54, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                  · linarith only [h0, h2, h5, h54, h56, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h2, h4, h5, h56, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
            · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
              · linarith only [h1, h60, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
              · linarith only [h3, h4, h60, hc13, hc35, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
              · linarith only [h1, h63, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
              · linarith only [h3, h4, h63, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h66 | h66
          · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
            · rcases m.htr 1 3 4 (by decide) (by decide) with h68 | h68
              · linarith only [h3, h66, h68, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h70 | h70
                · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                  · linarith only [h0, h67, h71, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h3, h66, h71, hc23, hc34, hlam, hphi]
                · linarith only [h3, h66, h70, hc13, hc34, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h75 | h75
              · linarith only [h3, h66, h75, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
                · rcases m.htr 2 3 5 (by decide) (by decide) with h78 | h78
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                    · linarith only [h0, h2, h67, h77, h79, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                    · linarith only [h3, h66, h79, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                  · linarith only [h67, h77, h78, hlam]
                · linarith only [h3, h66, h77, hc13, hc34, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
            · rcases m.htr 1 3 4 (by decide) (by decide) with h85 | h85
              · linarith only [h3, h85, hlam, hphi, ht01, u0ehi7, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h87 | h87
                · linarith only [h0, h66, h84, h87, hlam, hphi, ht01, u0ehi7, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
                  · linarith only [h66, h89, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h91 | h91
                    · rcases h3bigk with h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h66, h91, hc13, hc34, hlam, hphi, p92_1]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h66, h91, hc23, hc34, hlam, hphi, p92_1]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h3, hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h66, hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h1, hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p92_1, u1elo0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h85, hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h87, hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h2, hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h84, hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h66, h91, hc23, hlam, hphi, ht01, ht12, p92_1, u0ehi7]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h89, hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p92_1, u0ehi7]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        rcases p92_3 (m.d 0 3) (by simp) with h109 | h109
                        · linarith only [h109, h3, hlam]
                        · linarith only [h1, h109, hlam]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        rcases p92_3 (m.d 0 3) (by simp) with h112 | h112
                        · linarith only [h112, h3, hlam]
                        · linarith only [h112, h2, hlam]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h66, hc34, hlam, hphi, ht01, ht12, ht23, p92_1, u0ehi7]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p92_1, u0ehi7]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        rcases p92_3 (m.d 0 3) (by simp) with h118 | h118
                        · linarith only [h118, h66, hlam]
                        · linarith only [h1, h118, hlam]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        rcases p92_3 (m.d 0 3) (by simp) with h121 | h121
                        · linarith only [h121, h66, hlam]
                        · linarith only [h121, h2, hlam]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [h91, hlam, p92_0]
                      · have p92_0 := h92c.1
                        have p92_1 := h92c.2.1
                        have p92_2 := h92c.2.2.1
                        have p92_3 := h92c.2.2.2
                        linarith only [hlam, p92_0]
                    · linarith only [h3, h91, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
              · linarith only [h127, h3, hlam, hphi, ht01, u0ehi7, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
                · linarith only [h0, h129, h2, h66, h84, hlam, hphi, ht01, u0ehi7, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                  · linarith only [h0, h131, h2, h66, hlam, hphi, ht01, u0ehi7, u1elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h133 | h133
                    · rcases h3bigk with h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h133, h66, hc13, hc34, hlam, hphi, p134_1]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h133, h66, h84, hc12, hc34, hlam, hphi, ht23, p134_1]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h3, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h66, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h1, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h84, hlam, p134_1]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h127, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h129, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h2, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h0, h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p134_1, u1elo0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h0, h133, h2, h66, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p134_1, u1elo0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h131, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p134_1, u0ehi7]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        rcases p134_3 (m.d 0 3) (by simp) with h151 | h151
                        · linarith only [h151, h3, hlam]
                        · linarith only [h1, h151, hlam]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h84, hc12, hc34, hlam, hphi, ht23, p134_1]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h0, h2, h66, h84, hc12, hc34, hlam, hphi, ht01, ht23, p134_1, u0ehi7, u1elo0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h0, h2, h84, hc12, hc35, hlam, hphi, ht01, ht23, p134_1, u0ehi7, u1elo0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        rcases p134_3 (m.d 0 3) (by simp) with h158 | h158
                        · linarith only [h158, h66, hlam]
                        · linarith only [h1, h158, hlam]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h133, h84, hc12, hc34, hlam, hphi, ht23, p134_1]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [h133, hlam, p134_0]
                      · have p134_0 := h134c.1
                        have p134_1 := h134c.2.1
                        have p134_2 := h134c.2.2.1
                        have p134_3 := h134c.2.2.2
                        linarith only [hlam, p134_0]
                    · linarith only [h0, h133, h2, h3, h84, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi7, u1elo0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h165 | h165
        · rcases m.htr 0 3 5 (by decide) (by decide) with h166 | h166
          · rcases m.htr 1 2 3 (by decide) (by decide) with h167 | h167
            · linarith only [h167, h2, hlam, hphi, ht01, u0ehi6, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
              · linarith only [h1, h169, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                · linarith only [h165, h169, h171, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h173 | h173
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h174 | h174
                    · linarith only [h1, h165, h174, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                    · rcases h3bigk with h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c | h176c
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        rcases p176_3 (m.d 0 3) (by simp) with h178 | h178
                        · rcases p176_3 (m.d 1 3) (by simp) with h179 | h179
                          · linarith only [h1, h179, hlam]
                          · rcases p176_3 (m.d 2 3) (by simp) with h181 | h181
                            · rcases p176_3 (m.d 3 4) (by simp) with h182 | h182
                              · linarith only [h165, h182, hlam]
                              · linarith only [h169, h182, hlam]
                            · linarith only [h167, h181, hlam]
                        · linarith only [h1, h178, hlam]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h2, hlam, p176_1]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h1, h169, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p176_1, u1elo0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h1, h167, h171, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p176_1, u1elo0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h1, hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h167, hlam, p176_1]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h169, hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h171, hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hc23, hlam, hphi, ht01, ht12, p176_1, u0ehi7]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        rcases p176_3 (m.d 0 3) (by simp) with h196 | h196
                        · linarith only [h196, h2, hlam]
                        · linarith only [h1, h196, hlam]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h167, h169, hc12, hc23, hlam, hphi, p176_1]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h167, h169, h174, hc12, hc23, hlam, hphi, p176_1]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h165, hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h1, h166, h167, h174, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p176_1, u1elo0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h1, h166, h174, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p176_1, u1elo0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h174, hlam, p176_1]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h166, hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h1, h166, h167, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p176_1, u1elo0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h173, hlam, p176_0]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [h1, h166, hlam, hphi, ht01, ht0b, ht45, ht5b, p176_1, u1elo0, u4ehi3]
                      · have p176_0 := h176c.1
                        have p176_1 := h176c.2.1
                        have p176_2 := h176c.2.2.1
                        have p176_3 := h176c.2.2.2
                        linarith only [hlam, p176_0]
                  · linarith only [h1, h166, h173, h2, hlam, hphi, ht01, u0ehi6, u1elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
            · linarith only [h2, h213, hlam, hphi, ht01, u0ehi6, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
              · linarith only [h1, h215, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
              · linarith only [h165, h166, h213, h215, hc12, hc35, hlam, hphi, ht23]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h218 | h218
          · rcases m.htr 1 2 3 (by decide) (by decide) with h219 | h219
            · linarith only [h2, h219, hlam, hphi, ht01, u0ehi6, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
              · linarith only [h1, h165, h221, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h223 | h223
                · rcases m.htr 2 3 5 (by decide) (by decide) with h224 | h224
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h225 | h225
                    · linarith only [h1, h223, h225, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                    · linarith only [h165, h2, h225, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                  · linarith only [h1, h2, h223, h224, hlam, hphi, ht01, u0ehi6, u1elo0]
                · linarith only [h165, h218, h219, h223, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h230 | h230
            · linarith only [h2, h230, hlam, hphi, ht01, u0ehi6, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
              · linarith only [h165, h232, hlam, hphi, ht01, u0ehi7, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h234 | h234
                · linarith only [h1, h2, h218, h234, hlam, hphi, ht01, u0ehi6, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h236 | h236
                  · linarith only [h2, h218, h236, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                  · linarith only [h2, h236, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
    · linarith only [h1, hlam, hphi, ht01, u0ehi5, u1elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem r1l7_20_11_13_14_M_LR_L_R_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0ehi := hb0.2.2.1
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h5, h6, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
              · linarith only [h0, h2, h3, h6, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
            · linarith only [h0, h2, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
              · linarith only [h0, h10, h11, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
              · linarith only [h11, h3, h4, hc35, hlam, hphi, ht12, ht23, u1ehi2]
            · linarith only [h0, h10, h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h15 | h15
          · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
              · linarith only [h16, h17, h3, hc12, hlam, hphi, ht01, u0ehi7]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                  · linarith only [h0, h15, h16, h20, h3, hlam, hphi, u0ehi9, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h0, h16, h22, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h15, h22, h3, hc23, hc34, hlam, hphi]
                · linarith only [h15, h19, h3, hc13, hc34, hlam, hphi]
            · linarith only [h0, h16, h2, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
            · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
              · linarith only [h27, h28, h3, hc12, hlam, hphi, ht01, u0ehi7]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                · linarith only [h0, h15, h27, h30, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                  · linarith only [h0, h27, h3, h32, hlam, hphi, u0ehi7, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                    · linarith only [h0, h15, h27, h34, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                      · rcases h3bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p37_1, u0elo2, u1ehi2]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h15, h36, hc23, hc34, hlam, hphi, p37_1]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h3, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h15, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h1, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1, u0elo0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h28, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h30, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h2, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h27, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h32, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h34, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p37_1, u0ehi7]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p37_1, u1ehi2]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          rcases p37_3 (m.d 0 3) (by simp) with h55 | h55
                          · linarith only [h3, h55, hlam]
                          · linarith only [h2, h55, hlam]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h0, h15, h27, hc34, hlam, hphi, ht12, ht23, p37_1, u0ehi7, u0elo0, u1ehi2]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h0, h27, hc35, hlam, hphi, ht12, ht23, p37_1, u0ehi7, u0elo0, u1ehi2]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p37_1, u1ehi2]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          rcases p37_3 (m.d 0 3) (by simp) with h62 | h62
                          · linarith only [h15, h62, hlam]
                          · linarith only [h2, h62, hlam]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [h36, hlam, p37_0]
                        · have p37_0 := h37c.1
                          have p37_1 := h37c.2.1
                          have p37_2 := h37c.2.2.1
                          have p37_3 := h37c.2.2.2
                          linarith only [hlam, p37_0]
                      · linarith only [h0, h27, h3, h36, hc45, hlam, hphi, ht12, ht23, ht34, u0ehi7, u0elo0, u1ehi2]
            · linarith only [h0, h2, h27, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h69 | h69
        · rcases m.htr 0 3 5 (by decide) (by decide) with h70 | h70
          · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
            · linarith only [h2, h71, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
              · linarith only [h1, h73, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
              · linarith only [h69, h71, h73, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
            · linarith only [h2, h76, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
              · linarith only [h1, h78, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
              · linarith only [h69, h70, h76, h78, hc35, hlam, hphi, ht12, ht23, u1ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h81 | h81
          · rcases m.htr 1 2 3 (by decide) (by decide) with h82 | h82
            · linarith only [h2, h82, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h84 | h84
              · linarith only [h1, h69, h84, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h86 | h86
                · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                  · linarith only [h1, h69, h81, h82, h87, hc23, hlam, hphi, ht12, u0ehi9, u0elo0, u1ehi1]
                  · linarith only [h1, h2, h82, h87, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
                · linarith only [h81, h82, h86, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
            · linarith only [h2, h91, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
              · linarith only [h1, h69, h93, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                · linarith only [h1, h2, h81, h95, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                  · linarith only [h1, h2, h69, h91, h97, hc23, hlam, hphi, ht12, u0ehi6, u0elo0, u1ehi1]
                  · linarith only [h1, h2, h91, h97, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h101 | h101
    · linarith only [h0, h101, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h103 | h103
      · rcases m.htr 0 3 4 (by decide) (by decide) with h104 | h104
        · rcases m.htr 0 3 5 (by decide) (by decide) with h105 | h105
          · rcases m.htr 1 2 3 (by decide) (by decide) with h106 | h106
            · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
              · rcases m.htr 1 3 5 (by decide) (by decide) with h108 | h108
                · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                  · linarith only [h103, h109, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
                    · linarith only [h104, h109, h111, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h113 | h113
                      · linarith only [h103, h104, h113, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · rcases h3bigk with h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [hlam, p115_0]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h101, hlam, p115_1]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          rcases p115_3 (m.d 0 3) (by simp) with h118 | h118
                          · rcases p115_3 (m.d 1 3) (by simp) with h119 | h119
                            · rcases p115_3 (m.d 2 3) (by simp) with h120 | h120
                              · linarith only [h103, h120, hlam]
                              · rcases p115_3 (m.d 3 4) (by simp) with h122 | h122
                                · linarith only [h104, h122, hlam]
                                · linarith only [h109, h122, hlam]
                            · linarith only [h106, h119, hlam]
                          · linarith only [h103, h118, hlam]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h103, h109, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p115_1, u0elo1]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h103, h111, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p115_1, u0elo1]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h106, hc12, hlam, hphi, ht01, p115_1, u0ehi7]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [hlam, p115_0]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          rcases p115_3 (m.d 0 3) (by simp) with h131 | h131
                          · linarith only [h101, h131, hlam]
                          · linarith only [h103, h131, hlam]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          rcases p115_3 (m.d 0 3) (by simp) with h134 | h134
                          · linarith only [h101, h134, hlam]
                          · linarith only [h104, h134, hlam]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          rcases p115_3 (m.d 0 3) (by simp) with h137 | h137
                          · linarith only [h101, h137, hlam]
                          · linarith only [h105, h137, hlam]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h103, hlam, p115_0]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h106, hlam, p115_0]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [hlam, p115_0]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h109, hlam, p115_0]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h111, hlam, p115_0]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h104, hlam, p115_0]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h107, hlam, p115_0]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h105, h113, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p115_1, u0elo2]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [hlam, p115_0]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h113, hlam, p115_1]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h105, hlam, p115_0]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h108, hlam, p115_0]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h103, h105, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p115_1, u0elo1]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [h103, h105, h109, hlam, hphi, ht0b, ht45, ht5b, p115_1, u0elo1, u4ehi2]
                        · have p115_0 := h115c.1
                          have p115_1 := h115c.2.1
                          have p115_2 := h115c.2.2.1
                          have p115_3 := h115c.2.2.2
                          linarith only [hlam, p115_0]
                · linarith only [h103, h105, h108, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi2]
              · linarith only [h101, h107, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
            · linarith only [h0, h106, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
            · rcases m.htr 1 3 4 (by decide) (by decide) with h159 | h159
              · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                · linarith only [h104, h105, h158, h160, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · linarith only [h101, h160, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
              · linarith only [h101, h104, h159, hlam, hphi, u0ehi5, u0elo2]
            · linarith only [h103, h158, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h165 | h165
          · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
            · rcases m.htr 1 3 4 (by decide) (by decide) with h167 | h167
              · linarith only [h101, h104, h166, h167, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h101, h167, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
            · linarith only [h103, h166, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
            · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
              · linarith only [h101, h104, h171, h172, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h101, h172, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
            · linarith only [h103, h171, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h176 | h176
        · rcases m.htr 0 3 5 (by decide) (by decide) with h177 | h177
          · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
            · linarith only [h0, h103, h178, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h178, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h181 | h181
            · linarith only [h0, h103, h181, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h181, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h184 | h184
          · rcases m.htr 1 2 3 (by decide) (by decide) with h185 | h185
            · linarith only [h0, h103, h185, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h185, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
            · linarith only [h0, h103, h188, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h188, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem r1l7_20_11_13_14_M_LR_L_R_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
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
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h1, h9, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h0, h4, h6, h9, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                  · linarith only [h0, h5, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h14 | h14
                    · linarith only [h1, h14, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h0, h14, h4, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                  · linarith only [h0, h13, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
                · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                    · linarith only [h20, h6, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                        · linarith only [h0, h23, h4, h6, hlam, hphi, u0ehi7, u0elo0]
                        · linarith only [h0, h19, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                      · linarith only [h18, h20, h22, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi2]
                  · linarith only [h0, h19, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                    · linarith only [h29, h6, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                      · linarith only [h0, h18, h28, h31, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                        · linarith only [h0, h28, h29, h33, h6, hc23, hlam, hphi, ht12, u0ehi7, u0elo0, u1ehi2]
                        · linarith only [h0, h28, h33, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                  · linarith only [h0, h28, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h37 | h37
              · linarith only [h37, h4, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h39 | h39
                · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
                  · linarith only [h40, h5, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h42 | h42
                    · linarith only [h2, h37, h40, h42, hc13, hlam, hphi, u0ehi7, u0elo0, u1ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h44 | h44
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                        · linarith only [h37, h4, h45, hlam, hphi, u0ehi7, u0elo1]
                        · linarith only [h4, h45, h5, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h2, h39, h40, h44, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
                · linarith only [h39, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h50 | h50
            · rcases m.htr 0 3 4 (by decide) (by decide) with h51 | h51
              · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
                · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                    · linarith only [h1, h54, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h51, h54, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h4, h50, h53, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h59 | h59
                    · linarith only [h1, h59, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h1, h51, h59, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                  · linarith only [h4, h50, h58, hc12, hc23, hlam, hphi]
              · linarith only [h4, h50, h51, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h64 | h64
              · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
                · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
                  · linarith only [h50, h66, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h68 | h68
                    · linarith only [h1, h68, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h64, h68, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
                  · linarith only [h50, h71, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                    · linarith only [h1, h73, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h1, h64, h73, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
                · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                  · linarith only [h50, h77, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                    · linarith only [h64, h79, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                        · linarith only [h2, h4, h64, h77, h82, hc23, hlam, hphi, ht12, u0ehi6, u0elo0, u1ehi1]
                        · linarith only [h2, h4, h77, h82, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
                      · linarith only [h76, h77, h81, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3, u1ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
                  · linarith only [h50, h86, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                    · linarith only [h1, h4, h64, h76, h88, hc45, hlam, hphi, ht34, u0ehi6, u0elo0, u3ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                      · linarith only [h2, h4, h64, h76, h90, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                        · linarith only [h3, h4, h64, h86, h90, h92, hc23, hlam, hphi, ht12, u0ehi6, u0elo0, u1ehi1]
                        · linarith only [h3, h4, h86, h90, h92, hc34, hlam, hphi, ht12, ht23, u0ehi6, u0elo0, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h98 | h98
    · linarith only [h0, h98, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h100 | h100
      · linarith only [h0, h100, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h102 | h102
        · linarith only [h0, h102, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h104 | h104
          · rcases m.htr 0 2 4 (by decide) (by decide) with h105 | h105
            · rcases m.htr 0 3 4 (by decide) (by decide) with h106 | h106
              · rcases m.htr 0 4 5 (by decide) (by decide) with h107 | h107
                · rcases m.htr 1 2 4 (by decide) (by decide) with h108 | h108
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h109 | h109
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                        · linarith only [h104, h111, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h104, h106, h111, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                      · linarith only [h104, h106, h107, h110, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi3]
                    · linarith only [h104, h106, h109, h98, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                  · linarith only [h0, h105, h108, hlam, hphi, u0ehi5, u0elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                      · linarith only [h107, h117, h119, hc12, hlam, hphi, ht01, u0ehi8]
                      · linarith only [h100, h119, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                    · linarith only [h104, h106, h118, h98, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h105, h117, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h124 | h124
                · rcases m.htr 1 2 4 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                    · linarith only [h106, h126, h98, hc13, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h126, h98, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                  · linarith only [h105, h125, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h130 | h130
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h131 | h131
                    · linarith only [h106, h131, h98, hc13, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h131, h98, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                  · linarith only [h105, h106, h124, h130, h98, hc45, hlam, hphi, ht12, ht23, ht34, u0ehi5, u0elo1, u1ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h135 | h135
              · linarith only [h104, h105, h135, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h137 | h137
                · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
                  · linarith only [h105, h138, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h138, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h104, h105, h137, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h142 | h142
            · rcases m.htr 0 3 4 (by decide) (by decide) with h143 | h143
              · rcases m.htr 0 4 5 (by decide) (by decide) with h144 | h144
                · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h147 | h147
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h149 | h149
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h150 | h150
                            · rcases h4bigk with h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [hlam, p151_0]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h100, hlam, p151_0]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h142, h148, h150, hlam, hphi, ht0b, ht34, ht45, ht5b, p151_1, u0elo1, u3ehi4]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h104, h142, h150, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p151_1, u3ehi4]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                rcases p151_3 (m.d 0 4) (by simp) with h156 | h156
                                · rcases p151_3 (m.d 1 4) (by simp) with h157 | h157
                                  · rcases p151_3 (m.d 2 4) (by simp) with h158 | h158
                                    · linarith only [h142, h158, hlam]
                                    · linarith only [h149, h158, hlam]
                                  · linarith only [h147, h157, hlam]
                                · linarith only [h156, hlam, p151_0]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h145, hc12, hlam, hphi, ht01, p151_1, u0ehi8]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [hlam, p151_0]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                rcases p151_3 (m.d 0 4) (by simp) with h165 | h165
                                · linarith only [h100, h165, hlam]
                                · linarith only [h142, h165, hlam]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                rcases p151_3 (m.d 0 4) (by simp) with h168 | h168
                                · linarith only [h100, h168, hlam]
                                · linarith only [h143, h168, hlam]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                rcases p151_3 (m.d 0 4) (by simp) with h171 | h171
                                · linarith only [h100, h171, hlam]
                                · linarith only [h144, h171, hlam]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h142, hlam, p151_1]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h145, hlam, p151_1]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [hlam, p151_0]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h104, h142, h150, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p151_1, u3ehi4]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h104, h142, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p151_1]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h143, hlam, p151_1]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h146, hlam, p151_0]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h148, hlam, p151_0]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [hlam, p151_0]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h143, hc45, hlam, hphi, ht0b, ht5b, p151_1, u0elo2]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h144, hlam, p151_0]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h147, hlam, p151_0]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h149, hlam, p151_0]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [h150, hlam, p151_0]
                              · have p151_0 := h151c.1
                                have p151_1 := h151c.2.1
                                have p151_2 := h151c.2.2.1
                                have p151_3 := h151c.2.2.2
                                linarith only [hlam, p151_0]
                            · linarith only [h144, h150, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                          · linarith only [h104, h142, h144, h148, h149, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h104, h148, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                      · linarith only [h142, h144, h147, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi3]
                    · linarith only [h143, h146, h98, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2, u1ehi0]
                  · linarith only [h0, h145, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h195 | h195
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h196 | h196
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h197 | h197
                      · linarith only [h144, h195, h197, hc12, hlam, hphi, ht01, u0ehi8]
                      · linarith only [h100, h197, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                    · linarith only [h143, h196, h98, hlam, hphi, u0ehi5, u0elo2]
                  · linarith only [h104, h142, h195, hc12, hc23, hlam, hphi]
              · linarith only [h104, h142, h143, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h203 | h203
              · rcases m.htr 0 4 5 (by decide) (by decide) with h204 | h204
                · rcases m.htr 1 2 4 (by decide) (by decide) with h205 | h205
                  · linarith only [h142, h205, hc12, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h205, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
                  · linarith only [h0, h142, h208, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h208, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h211 | h211
                · rcases m.htr 1 2 4 (by decide) (by decide) with h212 | h212
                  · linarith only [h0, h142, h212, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h212, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h215 | h215
                  · linarith only [h0, h142, h215, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h215, hc24, hlam, hphi, ht01, ht12, u0ehi5]

theorem r1l7_20_11_13_M_LR_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h12, h4, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                          · linarith only [h0, h15, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h15, h4, hc23, hlam, hphi, u3elo0]
                      · linarith only [h10, h5, hc13, hlam, hphi, u3elo0]
                    · linarith only [h4, h6, h9, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                      · linarith only [h21, h6, h8, hlam]
                      · linarith only [h21, h5, hc13, hlam, hphi, u3elo0]
                    · linarith only [h20, h4, h6, hc23, hlam, hphi, u3elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                    · linarith only [h26, h6, h7, hlam]
                    · linarith only [h26, h4, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                    · linarith only [h29, h6, h7, hlam]
                    · linarith only [h29, h4, hc13, hlam, hphi, u3elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                · linarith only [h0, h3, h32, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                  · linarith only [h0, h3, h34, h6, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
                                · linarith only [h0, h3, h36, h42, h6, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h0, h3, h36, h38, h42, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h0, h3, h36, h38, h41, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h37, h40, h6, hlam]
                          · linarith only [h36, h38, h39, h4, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                              · linarith only [h0, h3, h32, h38, h48, h50, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                                · linarith only [h36, h50, h52, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
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
                                    rcases p54_3 (m.d 0 1) (by simp) with h56 | h56
                                    · rcases p54_3 (m.d 1 2) (by simp) with h57 | h57
                                      · linarith only [h57, hlam, p54_0]
                                      · rcases p54_3 (m.d 1 3) (by simp) with h59 | h59
                                        · linarith only [h1, h59, hlam]
                                        · linarith only [h59, h6, hlam]
                                    · linarith only [h56, hlam, p54_0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h36, hc34, hlam, hphi, ht0b, ht45, ht5b, p54_1, u0elo0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    rcases p54_3 (m.d 0 1) (by simp) with h64 | h64
                                    · rcases p54_3 (m.d 1 2) (by simp) with h65 | h65
                                      · linarith only [h0, h65, hlam]
                                      · rcases p54_3 (m.d 1 3) (by simp) with h67 | h67
                                        · linarith only [h1, h67, hlam]
                                        · linarith only [h36, h67, hlam]
                                    · linarith only [h64, hlam, p54_0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    rcases p54_3 (m.d 0 1) (by simp) with h71 | h71
                                    · rcases p54_3 (m.d 1 2) (by simp) with h72 | h72
                                      · linarith only [h0, h72, hlam]
                                      · rcases p54_3 (m.d 1 3) (by simp) with h74 | h74
                                        · linarith only [h1, h74, hlam]
                                        · linarith only [h37, h74, hlam]
                                    · linarith only [h71, hlam, p54_0]
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
                                    linarith only [h6, hlam, p54_0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h32, hlam, p54_0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h34, hlam, p54_0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h1, hlam, p54_0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht23, p54_1, u3elo1]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [hlam, p54_0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h0, h3, h32, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p54_1, u0elo0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h0, h3, h32, h38, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p54_1, u0elo0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h2, hlam, p54_0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p54_1, u0elo0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h36, hlam, p54_0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [hlam, p54_0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h38, hlam, p54_1]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [hc15, hlam, hphi, ht01, p54_1, u0ehi5]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h0, h3, h37, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p54_1, u0elo0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h37, hlam, p54_0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [h0, h3, h32, h37, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p54_1, u0elo0]
                                  · have p54_0 := h54c.1
                                    have p54_1 := h54c.2.1
                                    have p54_2 := h54c.2.2.1
                                    have p54_3 := h54c.2.2.2
                                    linarith only [hlam, p54_0]
                            · linarith only [h49, h5, h6, hc13, hlam, hphi, u3elo0]
                          · linarith only [h48, h6, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h37, h5, hc13, hlam, hphi, u3elo0]
                    · linarith only [h36, h4, h6, hc12, hlam, hphi, ht23, u3elo0]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h105 | h105
        · rcases m.htr 0 3 4 (by decide) (by decide) with h106 | h106
          · linarith only [h0, h105, h106, h2, hlam]
          · linarith only [h106, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
        · linarith only [h105, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h111 | h111
    · rcases m.htr 0 1 4 (by decide) (by decide) with h112 | h112
      · rcases m.htr 0 2 3 (by decide) (by decide) with h113 | h113
        · rcases m.htr 0 3 4 (by decide) (by decide) with h114 | h114
          · rcases m.htr 0 3 5 (by decide) (by decide) with h115 | h115
            · rcases m.htr 1 2 3 (by decide) (by decide) with h116 | h116
              · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
                · rcases m.htr 1 2 5 (by decide) (by decide) with h118 | h118
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h120 | h120
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h123 | h123
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h124 | h124
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h125 | h125
                                · linarith only [h111, h116, h122, h125, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h0, h111, h119, h121, h125, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h0, h111, h119, h121, h124, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h115, h123, hc23, hlam, hphi, u3elo0]
                          · linarith only [h114, h122, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
                              · linarith only [h117, h121, h133, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
                                · linarith only [h114, h121, h135, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                                · rcases h1bigk with h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c | h137c
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [hlam, p137_0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h0, hlam, p137_0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h0, h116, h132, hc35, hlam, hphi, ht0b, ht5b, p137_1, u0elo1]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    rcases p137_3 (m.d 0 1) (by simp) with h141 | h141
                                    · rcases p137_3 (m.d 1 2) (by simp) with h142 | h142
                                      · rcases p137_3 (m.d 1 3) (by simp) with h143 | h143
                                        · linarith only [h111, h143, hlam]
                                        · linarith only [h119, h143, hlam]
                                      · linarith only [h117, h142, hlam]
                                    · linarith only [h141, hlam, p137_0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    rcases p137_3 (m.d 0 1) (by simp) with h148 | h148
                                    · rcases p137_3 (m.d 1 2) (by simp) with h149 | h149
                                      · rcases p137_3 (m.d 1 3) (by simp) with h150 | h150
                                        · linarith only [h111, h150, hlam]
                                        · linarith only [h120, h150, hlam]
                                      · linarith only [h118, h149, hlam]
                                    · linarith only [h148, hlam, p137_0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p137_1, u0ehi5]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [hlam, p137_0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    rcases p137_3 (m.d 0 1) (by simp) with h157 | h157
                                    · linarith only [h0, h157, hlam]
                                    · linarith only [h111, h157, hlam]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    rcases p137_3 (m.d 0 1) (by simp) with h160 | h160
                                    · linarith only [h0, h160, hlam]
                                    · linarith only [h112, h160, hlam]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    rcases p137_3 (m.d 0 1) (by simp) with h163 | h163
                                    · linarith only [h0, h163, hlam]
                                    · linarith only [h163, hc12, hlam, hphi, ht01, p137_1, u0ehi5]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h111, hlam, p137_0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h116, hlam, p137_1]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [hlam, p137_0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h111, hc14, hlam, hphi, ht0b, ht45, ht5b, p137_1, u0elo0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h0, h111, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p137_1]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h112, hlam, p137_0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h117, hlam, p137_1]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h119, hlam, p137_0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [hlam, p137_0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h121, hlam, p137_1]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [hc15, hlam, hphi, ht01, p137_1, u0ehi5]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h118, hlam, p137_1]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h120, hlam, p137_0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [h111, h117, h120, h131, hc34, hlam, hphi, ht0b, ht45, ht5b, p137_1, u0elo0]
                                  · have p137_0 := h137c.1
                                    have p137_1 := h137c.2.1
                                    have p137_2 := h137c.2.2.1
                                    have p137_3 := h137c.2.2.2
                                    linarith only [hlam, p137_0]
                            · linarith only [h115, h132, hc23, hlam, hphi, u3elo0]
                          · linarith only [h114, h131, hc23, hlam, hphi, u3elo0]
                      · linarith only [h115, h120, hc13, hlam, hphi, u3elo0]
                    · linarith only [h114, h116, h119, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h118, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h117, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h111, h115, h116, hc23, hlam, hphi, ht01, ht12, u0ehi9]
            · linarith only [h115, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
          · linarith only [h114, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
        · linarith only [h113, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h191 | h191
        · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
          · linarith only [h111, h112, h192, hlam]
          · linarith only [h192, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
        · linarith only [h0, h111, h191, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo2]
    · linarith only [h111, hlam, hphi, ht01, ht12, ht23, u0ehi5, u3elo1]

theorem r1l7_20_12_13_15_H_I_L_0_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
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
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                          · linarith only [h1, h10, h12, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h11, h3, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                      · linarith only [h10, h3, h5, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                    · linarith only [h4, h9, hc12, hlam, hphi, u2elo0]
                  · linarith only [h3, h8, hc12, hlam, hphi, u2elo0]
                · linarith only [h5, h7, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h6, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
              · linarith only [h21, h5, hc34, hlam, hphi, u3ehi4]
              · linarith only [h21, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
          · linarith only [h3, h4, hlam, hphi, ht34, ht45, u3ehi2, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h25 | h25
          · rcases m.htr 0 3 4 (by decide) (by decide) with h26 | h26
            · rcases m.htr 0 3 5 (by decide) (by decide) with h27 | h27
              · rcases m.htr 0 4 5 (by decide) (by decide) with h28 | h28
                · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
                  · linarith only [h25, h27, h29, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                            · linarith only [h25, h3, h35, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                            · linarith only [h0, h2, h3, h31, h33, h35, hc25, hlam, hphi, u5elo0]
                          · linarith only [h1, h3, h32, h34, hlam]
                        · linarith only [h32, h33, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h26, h3, h32, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                    · linarith only [h25, h3, h31, hc12, hlam, hphi, u2elo2]
                · linarith only [h26, h28, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h27, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h44 | h44
              · linarith only [h26, h44, hc34, hlam, hphi, u3ehi4]
              · linarith only [h44, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h47 | h47
            · rcases m.htr 0 3 5 (by decide) (by decide) with h48 | h48
              · rcases m.htr 0 4 5 (by decide) (by decide) with h49 | h49
                · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
                  · linarith only [h3, h47, h50, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
                    · linarith only [h0, h25, h52, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h55 | h55
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                              · rcases h0bigk with h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [hlam, p59_0]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  rcases p59_3 (m.d 0 1) (by simp) with h61 | h61
                                  · rcases p59_3 (m.d 0 2) (by simp) with h62 | h62
                                    · linarith only [h0, h62, hlam]
                                    · rcases p59_3 (m.d 0 3) (by simp) with h64 | h64
                                      · linarith only [h1, h64, hlam]
                                      · linarith only [h3, h64, hlam]
                                  · linarith only [h0, h61, hlam]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h1, h54, h58, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1, u3ehi4]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h2, h49, h55, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1, u3ehi4]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h2, h55, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1, u3ehi4]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h0, hlam, p59_0]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [hlam, p59_0]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h3, hlam, p59_0]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h2, h49, h55, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1, u3ehi4]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h25, hlam, p59_0]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h1, hlam, p59_1]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h0, h3, hc12, hlam, hphi, p59_1, u2elo2]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [hlam, p59_0]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h2, h3, h49, h55, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p59_1, u2elo2, u3ehi4]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h2, h3, h55, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p59_1, u2elo2, u3ehi4]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p59_1]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h0, h3, h47, hc12, hlam, hphi, p59_1, u2elo2]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h47, hlam, p59_0]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [hlam, p59_0]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h2, h3, h47, h55, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p59_1, u2elo2, u3ehi4]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h2, hlam, p59_0]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p59_1, u5elo0]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h48, hlam, p59_0]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [h49, hlam, p59_1]
                                · have p59_0 := h59c.1
                                  have p59_1 := h59c.2.1
                                  have p59_2 := h59c.2.2.1
                                  have p59_3 := h59c.2.2.2
                                  linarith only [hlam, p59_0]
                              · linarith only [h3, h47, h49, h58, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                            · linarith only [h3, h55, h57, hlam, hphi, ht34, ht45, u3ehi0, u5elo1]
                          · linarith only [h1, h3, h54, h56, hlam]
                        · linarith only [h54, h55, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h3, h47, h54, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                · linarith only [h47, h49, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h48, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h98 | h98
              · linarith only [h47, h98, hc34, hlam, hphi, u3ehi4]
              · linarith only [h98, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
      · linarith only [h1, h2, hlam, hphi, ht34, ht45, u3ehi1, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h102 | h102
      · rcases m.htr 0 2 3 (by decide) (by decide) with h103 | h103
        · linarith only [h0, h1, h103, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h105 | h105
          · rcases m.htr 0 3 4 (by decide) (by decide) with h106 | h106
            · rcases m.htr 0 3 5 (by decide) (by decide) with h107 | h107
              · rcases m.htr 0 4 5 (by decide) (by decide) with h108 | h108
                · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
                  · linarith only [h103, h105, h107, h109, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                  · linarith only [h0, h1, h109, hc12, hlam, hphi, u2elo2]
                · linarith only [h106, h108, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h107, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h114 | h114
              · linarith only [h106, h114, hc34, hlam, hphi, u3ehi4]
              · linarith only [h114, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h117 | h117
            · rcases m.htr 0 3 5 (by decide) (by decide) with h118 | h118
              · rcases m.htr 0 4 5 (by decide) (by decide) with h119 | h119
                · rcases m.htr 1 2 3 (by decide) (by decide) with h120 | h120
                  · linarith only [h0, h103, h117, h120, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1, h120, hc12, hlam, hphi, u2elo2]
                · linarith only [h117, h119, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h117, h118, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h125 | h125
              · linarith only [h117, h125, hc34, hlam, hphi, u3ehi4]
              · linarith only [h125, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
      · linarith only [h0, h102, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h129 | h129
    · linarith only [h0, h129, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h131 | h131
      · rcases m.htr 0 2 3 (by decide) (by decide) with h132 | h132
        · rcases m.htr 0 2 5 (by decide) (by decide) with h133 | h133
          · rcases m.htr 0 3 4 (by decide) (by decide) with h134 | h134
            · rcases m.htr 0 3 5 (by decide) (by decide) with h135 | h135
              · rcases m.htr 0 4 5 (by decide) (by decide) with h136 | h136
                · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h138 | h138
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h139 | h139
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h140 | h140
                        · linarith only [h129, h131, h137, h140, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                        · linarith only [h129, h132, h134, h140, hc01, hlam, hphi, ht12, ht34, ht45, u2elo0, u3ehi3, u5elo3]
                      · linarith only [h129, h134, h139, hlam]
                    · linarith only [h0, h132, h134, h138, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi3]
                  · linarith only [h0, h132, h134, h137, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                · linarith only [h134, h136, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h134, h135, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h148 | h148
              · linarith only [h134, h148, hc34, hlam, hphi, u3ehi4]
              · linarith only [h148, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
          · linarith only [h132, h133, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h152 | h152
          · rcases m.htr 0 3 4 (by decide) (by decide) with h153 | h153
            · rcases m.htr 0 3 5 (by decide) (by decide) with h154 | h154
              · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
                · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                  · linarith only [h132, h156, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h156, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h153, h155, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h153, h154, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h161 | h161
              · linarith only [h153, h161, hc34, hlam, hphi, u3ehi4]
              · linarith only [h161, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
          · linarith only [h0, h131, h152, hc15, hlam, hphi, u5elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h165 | h165
        · rcases m.htr 0 2 5 (by decide) (by decide) with h166 | h166
          · rcases m.htr 0 3 4 (by decide) (by decide) with h167 | h167
            · rcases m.htr 0 3 5 (by decide) (by decide) with h168 | h168
              · rcases m.htr 0 4 5 (by decide) (by decide) with h169 | h169
                · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h171 | h171
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                          · linarith only [h0, h165, h174, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                          · linarith only [h0, h165, h167, h174, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                        · linarith only [h129, h168, h173, hlam, hphi, ht34, ht45, u3ehi0, u5elo0]
                      · linarith only [h129, h167, h172, hlam]
                    · linarith only [h0, h166, h171, hlam]
                  · linarith only [h0, h170, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h167, h169, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h167, h168, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h183 | h183
              · linarith only [h167, h183, hc34, hlam, hphi, u3ehi4]
              · linarith only [h183, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
          · linarith only [h165, h166, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h187 | h187
          · rcases m.htr 0 3 4 (by decide) (by decide) with h188 | h188
            · rcases m.htr 0 3 5 (by decide) (by decide) with h189 | h189
              · rcases m.htr 0 4 5 (by decide) (by decide) with h190 | h190
                · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
                  · linarith only [h165, h191, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h191, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h188, h190, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h188, h189, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h196 | h196
              · linarith only [h188, h196, hc34, hlam, hphi, u3ehi4]
              · linarith only [h196, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h199 | h199
            · rcases m.htr 0 3 5 (by decide) (by decide) with h200 | h200
              · rcases m.htr 0 4 5 (by decide) (by decide) with h201 | h201
                · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
                  · linarith only [h165, h199, h202, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                  · linarith only [h0, h202, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h199, h201, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
              · linarith only [h199, h200, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h207 | h207
              · linarith only [h199, h207, hc34, hlam, hphi, u3ehi4]
              · linarith only [h207, hlam, hphi, ht34, ht45, u3ehi0, u5elo3]

end R2N4
