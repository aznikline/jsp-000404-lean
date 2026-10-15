import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_I_L_I_L_0_H_L_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h12, h15, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
                              · linarith only [h15, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h11, h14, h3, hc24, hlam, hphi, ht45, u5elo0]
                          · linarith only [h13, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h0, h12, h20, h6, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h20, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h11, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h10, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
                        · linarith only [h0, h25, h27, h4, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                              · rcases h1bigk with h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h29, h31, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p32_1]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  rcases p32_3 (m.d 0 1) (by simp) with h35 | h35
                                  · rcases p32_3 (m.d 1 2) (by simp) with h36 | h36
                                    · linarith only [h0, h36, hlam]
                                    · linarith only [h36, h6, hlam]
                                  · linarith only [h35, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  rcases p32_3 (m.d 0 1) (by simp) with h40 | h40
                                  · rcases p32_3 (m.d 1 2) (by simp) with h41 | h41
                                    · linarith only [h0, h41, hlam]
                                    · linarith only [h41, h7, hlam]
                                  · linarith only [h40, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  rcases p32_3 (m.d 0 1) (by simp) with h45 | h45
                                  · rcases p32_3 (m.d 1 2) (by simp) with h46 | h46
                                    · linarith only [h0, h46, hlam]
                                    · linarith only [h46, h8, hlam]
                                  · linarith only [h45, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h0, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h0, h29, h31, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p32_1]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h0, h29, h31, h6, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p32_1]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  rcases p32_3 (m.d 0 1) (by simp) with h54 | h54
                                  · rcases p32_3 (m.d 1 2) (by simp) with h55 | h55
                                    · rcases p32_3 (m.d 1 3) (by simp) with h56 | h56
                                      · linarith only [h56, h6, hlam]
                                      · linarith only [h25, h56, hlam]
                                    · linarith only [h55, h8, hlam]
                                  · linarith only [h3, h54, hlam]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h1, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h6, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h9, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h8, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p32_1, u4elo3]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h2, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h7, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [hc13, hlam, hphi, ht34, p32_1, u4elo1]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  rcases p32_3 (m.d 0 1) (by simp) with h70 | h70
                                  · rcases p32_3 (m.d 1 2) (by simp) with h71 | h71
                                    · rcases p32_3 (m.d 1 3) (by simp) with h72 | h72
                                      · linarith only [h72, h9, hlam]
                                      · linarith only [h25, h72, hlam]
                                    · linarith only [h71, h8, hlam]
                                  · linarith only [h3, h70, hlam]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h3, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h8, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h25, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [h26, hlam, p32_0]
                                · have p32_0 := h32c.1
                                  have p32_1 := h32c.2.1
                                  have p32_2 := h32c.2.2.1
                                  have p32_3 := h32c.2.2.2
                                  linarith only [hlam, p32_0]
                              · linarith only [h31, h9, hc14, hlam, hphi, ht45, u5elo4]
                            · linarith only [h30, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h29, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h25, h26, h9, hc35, hlam, hphi, u5elo4]
                    · linarith only [h25, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h6, h7, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
              · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                            · linarith only [h0, h4, h6, h89, h96, hc01, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h93, h94, h96, hc34, hlam, hphi, u4elo1]
                          · linarith only [h6, h95, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h6, h94, hc12, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h93, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h6, h92, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h6, h89, h91, hc24, hlam, hphi, u4elo3]
                · linarith only [h89, h90, hc24, hlam, hphi, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h105 | h105
                · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h111 | h111
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                              · rcases h1bigk with h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c | h113c
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  rcases p113_3 (m.d 0 1) (by simp) with h115 | h115
                                  · rcases p113_3 (m.d 1 2) (by simp) with h116 | h116
                                    · linarith only [h116, hlam, p113_0]
                                    · rcases p113_3 (m.d 1 3) (by simp) with h118 | h118
                                      · linarith only [h1, h118, hlam]
                                      · linarith only [h118, h6, hlam]
                                  · linarith only [h115, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h106, h112, hc01, hc45, hlam, hphi, ht0b, ht5b, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  rcases p113_3 (m.d 0 1) (by simp) with h123 | h123
                                  · rcases p113_3 (m.d 1 2) (by simp) with h124 | h124
                                    · linarith only [h0, h124, hlam]
                                    · rcases p113_3 (m.d 1 3) (by simp) with h126 | h126
                                      · linarith only [h1, h126, hlam]
                                      · linarith only [h106, h126, hlam]
                                  · linarith only [h123, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  rcases p113_3 (m.d 0 1) (by simp) with h130 | h130
                                  · rcases p113_3 (m.d 1 2) (by simp) with h131 | h131
                                    · linarith only [h0, h131, hlam]
                                    · linarith only [h105, h131, hlam]
                                  · linarith only [h130, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h0, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h6, hlam, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h89, hlam, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h5, h89, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p113_1, u4elo0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h1, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h1, h105, hc01, hc25, hlam, hphi, ht0b, ht5b, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h105, h110, h112, h4, h6, h89, hc02, hc45, hlam, hphi, ht0b, ht5b, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  rcases p113_3 (m.d 0 1) (by simp) with h144 | h144
                                  · rcases p113_3 (m.d 1 2) (by simp) with h145 | h145
                                    · linarith only [h145, h6, hlam]
                                    · linarith only [h105, h145, hlam]
                                  · linarith only [h144, h3, hlam]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h2, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h105, h110, h112, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p113_1, u4elo1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h106, hlam, p113_1]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  rcases p113_3 (m.d 0 1) (by simp) with h153 | h153
                                  · rcases p113_3 (m.d 1 2) (by simp) with h154 | h154
                                    · linarith only [h154, h89, hlam]
                                    · linarith only [h105, h154, hlam]
                                  · linarith only [h153, h3, hlam]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h3, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h105, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h107, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [h108, hlam, p113_0]
                                · have p113_0 := h113c.1
                                  have p113_1 := h113c.2.1
                                  have p113_2 := h113c.2.2.1
                                  have p113_3 := h113c.2.2.2
                                  linarith only [hlam, p113_0]
                              · linarith only [h112, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h108, h111, h89, hc14, hlam, hphi, ht45, u5elo1]
                          · linarith only [h110, h6, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h105, h106, h109, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h105, h108, h89, hc25, hlam, hphi, u5elo4]
                    · linarith only [h107, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h169 | h169
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h170 | h170
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h171 | h171
                        · linarith only [h0, h105, h106, h171, h4, h6, hc01, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h105, h171, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h105, h106, h170, h6, hc25, hlam, hphi, u5elo4]
                    · linarith only [h105, h169, h6, hc25, hlam, hphi, u5elo3]
                · linarith only [h105, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h178 | h178
          · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
            · linarith only [h0, h178, h179, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
              · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
                · rcases m.htr 1 3 4 (by decide) (by decide) with h183 | h183
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h185 | h185
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h186 | h186
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h187 | h187
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h188 | h188
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h189 | h189
                              · rcases h1bigk with h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c | h190c
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h181, h186, h189, hc01, hc45, hlam, hphi, ht0b, ht5b, p190_1]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h179, h181, h186, h189, hc01, hc45, hlam, hphi, ht0b, ht5b, p190_1]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  rcases p190_3 (m.d 0 1) (by simp) with h194 | h194
                                  · rcases p190_3 (m.d 1 2) (by simp) with h195 | h195
                                    · linarith only [h0, h195, hlam]
                                    · linarith only [h181, h195, hlam]
                                  · linarith only [h194, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  rcases p190_3 (m.d 0 1) (by simp) with h199 | h199
                                  · rcases p190_3 (m.d 1 2) (by simp) with h200 | h200
                                    · linarith only [h0, h200, hlam]
                                    · linarith only [h182, h200, hlam]
                                  · linarith only [h199, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h0, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h179, hlam, p190_1]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h0, h181, h186, h189, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  rcases p190_3 (m.d 0 1) (by simp) with h208 | h208
                                  · rcases p190_3 (m.d 1 2) (by simp) with h209 | h209
                                    · rcases p190_3 (m.d 1 3) (by simp) with h210 | h210
                                      · rcases p190_3 (m.d 1 4) (by simp) with h211 | h211
                                        · linarith only [h181, h211, hlam]
                                        · linarith only [h185, h211, hlam]
                                      · linarith only [h184, h210, hlam]
                                    · linarith only [h182, h209, hlam]
                                  · linarith only [h208, h3, hlam]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h1, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h1, h181, h186, h189, hc01, hc45, hlam, hphi, ht0b, ht5b, p190_1]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h1, h181, h186, h189, hc01, hc45, hlam, hphi, ht0b, ht5b, p190_1]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  rcases p190_3 (m.d 0 1) (by simp) with h221 | h221
                                  · rcases p190_3 (m.d 1 2) (by simp) with h222 | h222
                                    · linarith only [h179, h222, hlam]
                                    · linarith only [h182, h222, hlam]
                                  · linarith only [h221, h3, hlam]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h2, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h181, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h183, hlam, p190_1]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  rcases p190_3 (m.d 0 1) (by simp) with h230 | h230
                                  · rcases p190_3 (m.d 1 2) (by simp) with h231 | h231
                                    · rcases p190_3 (m.d 1 3) (by simp) with h232 | h232
                                      · rcases p190_3 (m.d 1 4) (by simp) with h233 | h233
                                        · rcases p190_3 (m.d 1 5) (by simp) with h234 | h234
                                          · linarith only [h185, h234, hlam]
                                          · rcases h2bigk with h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [hlam, p236_0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h181, h182, h187, h189, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p190_1, p236_1]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h4, hlam, p236_0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h186, h189, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p236_1]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              rcases p236_3 (m.d 0 2) (by simp) with h241 | h241
                                              · rcases p236_3 (m.d 1 2) (by simp) with h242 | h242
                                                · linarith only [h0, h242, hlam]
                                                · linarith only [h182, h242, hlam]
                                              · linarith only [h241, hlam, p236_0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h0, hlam, p236_1]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [hlam, p236_0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h179, hlam, p236_0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h0, h186, h189, hc01, hc45, hlam, hphi, ht0b, ht5b, p236_1]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              rcases p236_3 (m.d 0 2) (by simp) with h250 | h250
                                              · rcases p236_3 (m.d 1 2) (by simp) with h251 | h251
                                                · rcases p236_3 (m.d 2 3) (by simp) with h252 | h252
                                                  · rcases p236_3 (m.d 2 4) (by simp) with h253 | h253
                                                    · linarith only [h181, h253, hlam]
                                                    · linarith only [h188, h253, hlam]
                                                  · linarith only [h187, h252, hlam]
                                                · linarith only [h251, hlam, p236_0]
                                              · linarith only [h0, h182, h2, h250, hc12, hlam, hphi, ht23, ht34, p190_1, u4elo0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h178, h186, h189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p236_1]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h181, h186, h189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p236_1]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [hlam, p236_0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              rcases p236_3 (m.d 0 2) (by simp) with h262 | h262
                                              · linarith only [h262, h4, hlam]
                                              · linarith only [h178, h262, hlam]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h178, h182, h2, h4, hlam, p190_1, p236_2]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h178, hlam, p236_0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h181, hlam, p236_0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h186, hlam, p236_0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [hlam, p236_0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h178, h187, h189, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p236_1]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h182, h2, hc02, hlam, hphi, ht23, ht34, p190_1, p236_1, u4elo0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h182, hlam, p236_0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h187, hlam, p236_0]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [h188, hlam, p236_1]
                                            · have p236_0 := h236c.1
                                              have p236_1 := h236c.2.1
                                              have p236_2 := h236c.2.2.1
                                              have p236_3 := h236c.2.2.2
                                              linarith only [hlam, p236_0]
                                        · linarith only [h185, h233, hlam]
                                      · linarith only [h184, h232, hlam]
                                    · linarith only [h182, h231, hlam]
                                  · linarith only [h230, h3, hlam]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h3, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h182, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h184, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [h185, hlam, p190_0]
                                · have p190_0 := h190c.1
                                  have p190_1 := h190c.2.1
                                  have p190_2 := h190c.2.2.1
                                  have p190_3 := h190c.2.2.2
                                  linarith only [hlam, p190_0]
                              · linarith only [h188, h189, hc34, hlam, hphi, u4elo2]
                            · linarith only [h185, h188, hc24, hlam, hphi, ht45, u5elo1]
                          · linarith only [h187, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h186, h4, hc02, hlam, hphi, ht23, ht34, u4elo3]
                      · linarith only [h185, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h184, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h179, h181, h183, hc24, hlam, hphi, u4elo3]
                · linarith only [h181, h182, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h178, h181, h4, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
            · linarith only [h0, h178, h294, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h296 | h296
              · linarith only [h0, h178, h296, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h298 | h298
                · rcases m.htr 1 3 4 (by decide) (by decide) with h299 | h299
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h300 | h300
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h301 | h301
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h302 | h302
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h303 | h303
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h304 | h304
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h305 | h305
                              · rcases h1bigk with h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  rcases p306_3 (m.d 0 1) (by simp) with h308 | h308
                                  · rcases p306_3 (m.d 1 2) (by simp) with h309 | h309
                                    · linarith only [h309, hlam, p306_0]
                                    · rcases p306_3 (m.d 1 3) (by simp) with h311 | h311
                                      · linarith only [h1, h311, hlam]
                                      · linarith only [h294, h311, hlam]
                                  · linarith only [h308, hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h299, h305, hc01, hc45, hlam, hphi, ht0b, ht5b, p306_1]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  rcases p306_3 (m.d 0 1) (by simp) with h316 | h316
                                  · rcases p306_3 (m.d 1 2) (by simp) with h317 | h317
                                    · linarith only [h0, h317, hlam]
                                    · rcases p306_3 (m.d 1 3) (by simp) with h319 | h319
                                      · linarith only [h1, h319, hlam]
                                      · linarith only [h299, h319, hlam]
                                  · linarith only [h316, hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  rcases p306_3 (m.d 0 1) (by simp) with h323 | h323
                                  · rcases p306_3 (m.d 1 2) (by simp) with h324 | h324
                                    · linarith only [h0, h324, hlam]
                                    · linarith only [h298, h324, hlam]
                                  · linarith only [h323, hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h0, hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h294, hlam, p306_1]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h296, hlam, p306_1]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h0, h178, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p306_1, u4elo2]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h1, hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h1, h298, hc01, hc25, hlam, hphi, ht0b, ht5b, p306_1]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h1, h296, h298, h303, hc01, hc35, hlam, hphi, ht0b, ht5b, p306_1]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  rcases p306_3 (m.d 0 1) (by simp) with h337 | h337
                                  · rcases p306_3 (m.d 1 2) (by simp) with h338 | h338
                                    · linarith only [h294, h338, hlam]
                                    · linarith only [h298, h338, hlam]
                                  · linarith only [h3, h337, hlam]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h2, hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h298, h303, h305, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p306_1, u4elo1]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h299, hlam, p306_1]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  rcases p306_3 (m.d 0 1) (by simp) with h346 | h346
                                  · rcases p306_3 (m.d 1 2) (by simp) with h347 | h347
                                    · linarith only [h296, h347, hlam]
                                    · linarith only [h298, h347, hlam]
                                  · linarith only [h3, h346, hlam]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h3, hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h298, hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h300, hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [h301, hlam, p306_0]
                                · have p306_0 := h306c.1
                                  have p306_1 := h306c.2.1
                                  have p306_2 := h306c.2.2.1
                                  have p306_3 := h306c.2.2.2
                                  linarith only [hlam, p306_0]
                              · linarith only [h305, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h178, h304, hc02, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h303, h4, hc03, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h1, h298, h299, h302, h4, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h296, h298, h301, hc25, hlam, hphi, u5elo4]
                    · linarith only [h0, h178, h298, h300, hc13, hc25, hlam, hphi, ht34, u4elo2, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h362 | h362
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h363 | h363
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h366 | h366
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h367 | h367
                              · rcases h1bigk with h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  rcases p368_3 (m.d 0 1) (by simp) with h370 | h370
                                  · rcases p368_3 (m.d 1 2) (by simp) with h371 | h371
                                    · linarith only [h371, hlam, p368_0]
                                    · rcases p368_3 (m.d 1 3) (by simp) with h373 | h373
                                      · linarith only [h1, h373, hlam]
                                      · linarith only [h294, h373, hlam]
                                  · linarith only [h370, hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  rcases p368_3 (m.d 0 1) (by simp) with h377 | h377
                                  · rcases p368_3 (m.d 1 2) (by simp) with h378 | h378
                                    · linarith only [h0, h378, hlam]
                                    · rcases p368_3 (m.d 1 3) (by simp) with h380 | h380
                                      · linarith only [h380, hlam, p368_0]
                                      · rcases p368_3 (m.d 1 4) (by simp) with h382 | h382
                                        · linarith only [h2, h382, hlam]
                                        · linarith only [h299, h382, hlam]
                                  · linarith only [h377, hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  rcases p368_3 (m.d 0 1) (by simp) with h386 | h386
                                  · rcases p368_3 (m.d 1 2) (by simp) with h387 | h387
                                    · linarith only [h0, h387, hlam]
                                    · rcases p368_3 (m.d 1 3) (by simp) with h389 | h389
                                      · linarith only [h1, h389, hlam]
                                      · rcases p368_3 (m.d 1 4) (by simp) with h391 | h391
                                        · linarith only [h391, hlam, p368_0]
                                        · rcases p368_3 (m.d 1 5) (by simp) with h393 | h393
                                          · linarith only [h3, h393, hlam]
                                          · rcases h2bigk with h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [hlam, p395_0]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h298, h365, h367, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p395_1]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h4, hlam, p395_0]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h178, hlam, p395_0]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h178, h365, h367, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p395_1, u4elo2]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h0, hlam, p395_1]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [hlam, p395_0]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h294, hlam, p395_0]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h296, hlam, p395_0]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h294, h299, h365, h367, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p395_1, u4elo3]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              rcases p395_3 (m.d 0 2) (by simp) with h406 | h406
                                              · linarith only [h406, hlam, p395_0]
                                              · rcases p395_3 (m.d 1 2) (by simp) with h408 | h408
                                                · linarith only [h294, h408, hlam]
                                                · rcases p395_3 (m.d 2 3) (by simp) with h410 | h410
                                                  · rcases p395_3 (m.d 2 4) (by simp) with h411 | h411
                                                    · linarith only [h364, h411, hlam]
                                                    · linarith only [h178, h411, hlam]
                                                  · linarith only [h410, hlam, p395_0]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              rcases p395_3 (m.d 0 2) (by simp) with h415 | h415
                                              · linarith only [h4, h415, hlam]
                                              · linarith only [h0, h415, hlam]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [hlam, p395_0]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h178, hc02, hc23, hlam, hphi, p395_1]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h294, h298, h299, h364, hlam, p395_2]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h0, h298, h365, h367, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p395_1, u4elo2]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h298, h365, h367, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p395_1, u4elo2]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h364, hlam, p395_0]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [hlam, p395_0]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              rcases p395_3 (m.d 0 2) (by simp) with h425 | h425
                                              · linarith only [h178, h425, hlam]
                                              · linarith only [h0, h298, h425, hlam]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h0, h298, hlam, p395_1]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h298, hlam, p395_0]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h365, hlam, p395_0]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [h366, hlam, p395_1]
                                            · have p395_0 := h395c.1
                                              have p395_1 := h395c.2.1
                                              have p395_2 := h395c.2.2.1
                                              have p395_3 := h395c.2.2.2
                                              linarith only [hlam, p395_0]
                                  · linarith only [h386, hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  rcases p368_3 (m.d 0 1) (by simp) with h434 | h434
                                  · rcases p368_3 (m.d 1 2) (by simp) with h435 | h435
                                    · linarith only [h0, h435, hlam]
                                    · linarith only [h298, h435, hlam]
                                  · linarith only [h434, hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h0, hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h294, hlam, p368_1]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h296, hlam, p368_1]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h294, h299, h364, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p368_1]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h1, hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h299, h364, hc12, hc23, hlam, hphi, p368_1]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h299, hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h298, h299, h365, h367, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p368_1, u4elo3]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h2, hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h2, h298, h365, h367, hc01, hc45, hlam, hphi, ht0b, ht5b, p368_1]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h178, h2, hc13, hlam, hphi, ht34, p368_1, u4elo2]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  rcases p368_3 (m.d 0 1) (by simp) with h453 | h453
                                  · rcases p368_3 (m.d 1 2) (by simp) with h454 | h454
                                    · linarith only [h296, h454, hlam]
                                    · linarith only [h298, h454, hlam]
                                  · linarith only [h3, h453, hlam]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h3, hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h298, hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h362, hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [h363, hlam, p368_0]
                                · have p368_0 := h368c.1
                                  have p368_1 := h368c.2.1
                                  have p368_2 := h368c.2.2.1
                                  have p368_3 := h368c.2.2.2
                                  linarith only [hlam, p368_0]
                              · linarith only [h367, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h178, h366, hc02, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h365, h4, hc03, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h298, h364, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h363, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h294, h298, h362, hc25, hlam, hphi, u5elo3]
                · linarith only [h298, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h472 | h472
    · rcases m.htr 0 1 5 (by decide) (by decide) with h473 | h473
      · rcases m.htr 0 2 3 (by decide) (by decide) with h474 | h474
        · linarith only [h0, h1, h474, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h476 | h476
          · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
            · linarith only [h0, h1, h474, h477, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h479 | h479
              · rcases m.htr 1 2 5 (by decide) (by decide) with h480 | h480
                · rcases m.htr 1 3 4 (by decide) (by decide) with h481 | h481
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h482 | h482
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h483 | h483
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h484 | h484
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h485 | h485
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h486 | h486
                            · linarith only [h0, h1, h477, h479, h486, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h484, h486, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h0, h1, h477, h479, h484, h485, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h477, h479, h484, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h483, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h1, h479, h482, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h479, h481, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h479, h480, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h0, h1, h476, h477, h479, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h496 | h496
            · linarith only [h0, h476, h496, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h498 | h498
              · linarith only [h0, h476, h498, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h500 | h500
                · rcases m.htr 1 3 4 (by decide) (by decide) with h501 | h501
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h502 | h502
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h503 | h503
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h504 | h504
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h505 | h505
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h506 | h506
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h507 | h507
                              · rcases h1bigk with h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c | h508c
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h1, h496, h500, h505, h507, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h1, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h1, h496, h498, h500, h505, h507, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  rcases p508_3 (m.d 0 1) (by simp) with h513 | h513
                                  · rcases p508_3 (m.d 1 2) (by simp) with h514 | h514
                                    · linarith only [h0, h514, hlam]
                                    · linarith only [h500, h514, hlam]
                                  · linarith only [h513, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h0, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h496, hlam, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h498, hlam, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h0, h1, h496, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h0, h496, hc12, hc23, hlam, hphi, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  rcases p508_3 (m.d 0 1) (by simp) with h524 | h524
                                  · linarith only [h1, h524, hlam]
                                  · linarith only [h0, h524, hlam]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  rcases p508_3 (m.d 0 1) (by simp) with h528 | h528
                                  · linarith only [h1, h528, hlam]
                                  · linarith only [h472, h528, hlam]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  rcases p508_3 (m.d 0 1) (by simp) with h531 | h531
                                  · linarith only [h1, h531, hlam]
                                  · linarith only [h473, h531, hlam]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h472, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h472, h500, h505, h507, hc01, hc45, hlam, hphi, ht0b, ht5b, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h501, hlam, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h1, h472, h496, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p508_1]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h473, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h500, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h502, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [h503, hlam, p508_0]
                                · have p508_0 := h508c.1
                                  have p508_1 := h508c.2.1
                                  have p508_2 := h508c.2.2.1
                                  have p508_3 := h508c.2.2.2
                                  linarith only [hlam, p508_0]
                              · linarith only [h507, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h1, h472, h476, h496, h500, h503, h505, h506, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h1, h472, h496, h503, h505, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h472, h496, h498, h500, h504, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h498, h500, h503, hc25, hlam, hphi, u5elo4]
                    · linarith only [h1, h472, h498, h500, h502, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h1, h472, h498, h500, h501, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h500, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h473, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h472, hc12, hlam, hphi, ht23, ht34, u4elo1]

end R2N4
