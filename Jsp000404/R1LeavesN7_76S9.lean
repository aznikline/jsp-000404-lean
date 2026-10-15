import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_M_IR_L_I_L_0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h11, h14, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h11, h13, h14, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h13, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                          · linarith only [h12, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                        · linarith only [h0, h11, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h9, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                        · linarith only [h22, h7, h9, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                              · rcases h2bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h0, h24, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p27_1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  rcases p27_3 (m.d 0 2) (by simp) with h30 | h30
                                  · rcases p27_3 (m.d 1 2) (by simp) with h31 | h31
                                    · linarith only [h0, h31, hlam]
                                    · linarith only [h31, h7, hlam]
                                  · linarith only [h30, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  rcases p27_3 (m.d 0 2) (by simp) with h35 | h35
                                  · rcases p27_3 (m.d 1 2) (by simp) with h36 | h36
                                    · linarith only [h0, h36, hlam]
                                    · linarith only [h0, h24, h36, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi4]
                                  · linarith only [h35, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  rcases p27_3 (m.d 0 2) (by simp) with h40 | h40
                                  · rcases p27_3 (m.d 1 2) (by simp) with h41 | h41
                                    · linarith only [h0, h41, hlam]
                                    · linarith only [h41, h8, hlam]
                                  · linarith only [h40, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h0, hlam, p27_1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h0, h24, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi4]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi4]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h2, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h7, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h22, hlam, p27_1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [hc23, hlam, hphi, p27_1, u2ehi4]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h3, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h22, h5, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h0, h2, h22, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi2]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h0, h2, h22, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi4]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h4, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h8, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h24, hlam, p27_0]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [h25, hlam, p27_1]
                                · have p27_0 := h27c.1
                                  have p27_1 := h27c.2.1
                                  have p27_2 := h27c.2.2.1
                                  have p27_3 := h27c.2.2.2
                                  linarith only [hlam, p27_0]
                              · linarith only [h22, h26, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                            · linarith only [h25, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                          · linarith only [h24, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h21, h6, h7, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo0]
                  · linarith only [h7, h8, hc25, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
                  · linarith only [h7, h70, hc23, hlam, hphi, u2ehi4]
                  · linarith only [h70, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
              · linarith only [h2, h6, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h74 | h74
              · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
                · rcases m.htr 1 2 5 (by decide) (by decide) with h76 | h76
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                    · linarith only [h1, h5, h77, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                        · linarith only [h1, h5, h75, h76, h79, h80, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h83 | h83
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h84 | h84
                              · rcases h2bigk with h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h0, h75, h82, hc01, hc35, hlam, hphi, ht0b, ht5b, p85_1]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  rcases p85_3 (m.d 0 2) (by simp) with h88 | h88
                                  · rcases p85_3 (m.d 1 2) (by simp) with h89 | h89
                                    · linarith only [h0, h89, hlam]
                                    · linarith only [h75, h89, hlam]
                                  · linarith only [h88, hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  rcases p85_3 (m.d 0 2) (by simp) with h93 | h93
                                  · rcases p85_3 (m.d 1 2) (by simp) with h94 | h94
                                    · linarith only [h0, h94, hlam]
                                    · linarith only [h0, h75, h82, h94, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p85_1, u2ehi4]
                                  · linarith only [h93, hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  rcases p85_3 (m.d 0 2) (by simp) with h98 | h98
                                  · rcases p85_3 (m.d 1 2) (by simp) with h99 | h99
                                    · linarith only [h0, h99, hlam]
                                    · linarith only [h76, h99, hlam]
                                  · linarith only [h98, hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h0, hlam, p85_1]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h0, h82, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p85_1, u2ehi4]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p85_1, u2ehi3]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p85_1, u2ehi4]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h2, hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h75, hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h80, hlam, p85_1]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [hc23, hlam, hphi, p85_1, u2ehi4]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h3, hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p85_1, u2ehi1]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p85_1, u2ehi2]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p85_1, u2ehi4]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h4, hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h76, hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h82, hlam, p85_0]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [h83, hlam, p85_1]
                                · have p85_0 := h85c.1
                                  have p85_1 := h85c.2.1
                                  have p85_2 := h85c.2.2.1
                                  have p85_3 := h85c.2.2.2
                                  linarith only [hlam, p85_0]
                              · linarith only [h3, h5, h84, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                            · linarith only [h83, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                          · linarith only [h82, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h5, h74, h79, hc13, hc34, hlam, hphi]
                  · linarith only [h75, h76, hc25, hlam, hphi, u2ehi2]
                · linarith only [h2, h5, h75, hc34, hlam, hphi, ht23, u2ehi1]
              · linarith only [h2, h74, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
          · linarith only [h4, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h132 | h132
        · linarith only [h132, h2, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h134 | h134
          · linarith only [h134, h2, hc23, hlam, hphi, u2ehi4]
          · linarith only [h134, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h137 | h137
      · linarith only [h0, h1, h137, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h139 | h139
        · linarith only [h137, h139, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h141 | h141
          · linarith only [h137, h141, hc23, hlam, hphi, u2ehi4]
          · linarith only [h141, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h144 | h144
    · rcases m.htr 0 2 3 (by decide) (by decide) with h145 | h145
      · rcases m.htr 0 2 4 (by decide) (by decide) with h146 | h146
        · rcases m.htr 0 2 5 (by decide) (by decide) with h147 | h147
          · rcases m.htr 0 3 4 (by decide) (by decide) with h148 | h148
            · rcases m.htr 0 3 5 (by decide) (by decide) with h149 | h149
              · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
                · rcases m.htr 1 2 5 (by decide) (by decide) with h151 | h151
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h155 | h155
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h156 | h156
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h157 | h157
                              · linarith only [h0, h144, h150, h154, h157, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h0, h144, h150, h154, h156, h157, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h156, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                          · linarith only [h155, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                        · linarith only [h0, h144, h148, h154, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h152, h153, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h0, h144, h148, h150, h152, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h151, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h145, h150, hlam]
              · linarith only [h146, h148, h149, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h168 | h168
              · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
                · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                    · linarith only [h0, h144, h148, h171, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
                        · linarith only [h144, h148, h169, h174, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h176 | h176
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h177 | h177
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h178 | h178
                              · rcases h2bigk with h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c | h179c
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h0, hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  rcases p179_3 (m.d 0 2) (by simp) with h182 | h182
                                  · rcases p179_3 (m.d 1 2) (by simp) with h183 | h183
                                    · rcases p179_3 (m.d 2 3) (by simp) with h184 | h184
                                      · linarith only [h184, hlam, p179_0]
                                      · rcases p179_3 (m.d 2 4) (by simp) with h186 | h186
                                        · linarith only [h146, h186, hlam]
                                        · linarith only [h174, h186, hlam]
                                    · linarith only [h169, h183, hlam]
                                  · linarith only [h182, hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  rcases p179_3 (m.d 0 2) (by simp) with h191 | h191
                                  · rcases p179_3 (m.d 1 2) (by simp) with h192 | h192
                                    · rcases p179_3 (m.d 2 3) (by simp) with h193 | h193
                                      · linarith only [h145, h193, hlam]
                                      · rcases p179_3 (m.d 2 4) (by simp) with h195 | h195
                                        · linarith only [h195, hlam, p179_0]
                                        · rcases p179_3 (m.d 2 5) (by simp) with h197 | h197
                                          · linarith only [h147, h197, hlam]
                                          · rcases h3bigk with h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [hlam, p199_0]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h148, h170, h173, hc34, hlam, hphi, ht23, p199_1, u2ehi4]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h148, hc23, hc34, hlam, hphi, p199_1]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h148, hlam, p199_0]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              rcases p199_3 (m.d 0 3) (by simp) with h204 | h204
                                              · rcases p199_3 (m.d 1 3) (by simp) with h205 | h205
                                                · linarith only [h144, h205, hlam]
                                                · linarith only [h173, h205, hlam]
                                              · linarith only [h204, hlam, p199_0]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h144, hlam, p199_0]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [hlam, p199_0]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h0, h144, h176, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p199_1, u2ehi4]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h171, hlam, p199_0]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h0, h144, h178, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p199_1]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h145, hlam, p199_1]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h169, hlam, p199_1]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [hlam, p199_0]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h174, hlam, p199_0]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h174, h178, hc02, hc45, hlam, hphi, ht0b, ht5b, p179_1, p199_1]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h145, hc34, hlam, hphi, ht23, p199_1, u2ehi2]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h169, hc34, hlam, hphi, ht23, p199_1, u2ehi2]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [hc34, hlam, hphi, ht23, p199_1, u2ehi2]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [hlam, p199_0]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              rcases p199_3 (m.d 0 3) (by simp) with h223 | h223
                                              · linarith only [h148, h223, hlam]
                                              · linarith only [h168, h223, hlam]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h168, hlam, p199_0]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h173, hlam, p199_0]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h176, hlam, p199_0]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [h178, hlam, p199_1]
                                            · have p199_0 := h199c.1
                                              have p199_1 := h199c.2.1
                                              have p199_2 := h199c.2.2.1
                                              have p199_3 := h199c.2.2.2
                                              linarith only [hlam, p199_0]
                                    · linarith only [h0, h192, hlam, p179_1]
                                  · linarith only [h191, hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  rcases p179_3 (m.d 0 2) (by simp) with h233 | h233
                                  · rcases p179_3 (m.d 1 2) (by simp) with h234 | h234
                                    · rcases p179_3 (m.d 2 3) (by simp) with h235 | h235
                                      · linarith only [h145, h235, hlam]
                                      · linarith only [h176, h235, hlam]
                                    · linarith only [h170, h234, hlam]
                                  · linarith only [h233, hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h0, h144, h170, h173, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p179_1, u2ehi4]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  rcases p179_3 (m.d 0 2) (by simp) with h242 | h242
                                  · linarith only [h0, h242, hlam]
                                  · linarith only [h145, h242, hlam]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  rcases p179_3 (m.d 0 2) (by simp) with h245 | h245
                                  · linarith only [h0, h245, hlam]
                                  · linarith only [h146, h245, hlam]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  rcases p179_3 (m.d 0 2) (by simp) with h248 | h248
                                  · linarith only [h0, h248, hlam]
                                  · linarith only [h147, h248, hlam]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h145, hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h169, hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h174, hlam, p179_1]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [hc23, hlam, hphi, p179_1, u2ehi4]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h146, hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h0, h146, hlam, p179_1]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h0, h146, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p179_1, u2ehi2]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h0, h146, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p179_1, u2ehi4]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h147, hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h170, hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h176, hlam, p179_0]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [h177, hlam, p179_1]
                                · have p179_0 := h179c.1
                                  have p179_1 := h179c.2.1
                                  have p179_2 := h179c.2.2.1
                                  have p179_3 := h179c.2.2.2
                                  linarith only [hlam, p179_0]
                              · linarith only [h144, h148, h170, h173, h178, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                            · linarith only [h177, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                          · linarith only [h176, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h148, h168, h173, hc13, hc34, hlam, hphi]
                  · linarith only [h0, h170, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
                · linarith only [h0, h147, h169, hc23, hlam, hphi, u2ehi4]
              · linarith only [h145, h168, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
          · linarith only [h147, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
        · linarith only [h145, h146, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h144, h145, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h276 | h276
      · rcases m.htr 0 2 4 (by decide) (by decide) with h277 | h277
        · rcases m.htr 0 2 5 (by decide) (by decide) with h278 | h278
          · rcases m.htr 0 3 4 (by decide) (by decide) with h279 | h279
            · rcases m.htr 0 3 5 (by decide) (by decide) with h280 | h280
              · rcases m.htr 1 2 3 (by decide) (by decide) with h281 | h281
                · rcases m.htr 1 2 5 (by decide) (by decide) with h282 | h282
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h283 | h283
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h284 | h284
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h285 | h285
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h286 | h286
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h287 | h287
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h288 | h288
                              · rcases h2bigk with h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h0, hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h285, h288, hc02, hc45, hlam, hphi, ht0b, ht5b, p289_1]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  rcases p289_3 (m.d 0 2) (by simp) with h293 | h293
                                  · rcases p289_3 (m.d 1 2) (by simp) with h294 | h294
                                    · rcases p289_3 (m.d 2 3) (by simp) with h295 | h295
                                      · linarith only [h276, h295, hlam]
                                      · linarith only [h285, h295, hlam]
                                    · linarith only [h0, h294, hlam, p289_1]
                                  · linarith only [h293, hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  rcases p289_3 (m.d 0 2) (by simp) with h300 | h300
                                  · rcases p289_3 (m.d 1 2) (by simp) with h301 | h301
                                    · rcases p289_3 (m.d 2 3) (by simp) with h302 | h302
                                      · linarith only [h276, h302, hlam]
                                      · linarith only [h286, h302, hlam]
                                    · linarith only [h282, h301, hlam]
                                  · linarith only [h300, hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h276, h285, h288, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p289_1]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h285, h288, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p289_1]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  rcases p289_3 (m.d 0 2) (by simp) with h310 | h310
                                  · linarith only [h0, h310, hlam]
                                  · linarith only [h277, h310, hlam]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  rcases p289_3 (m.d 0 2) (by simp) with h313 | h313
                                  · linarith only [h0, h313, hlam]
                                  · linarith only [h278, h313, hlam]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h276, hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h281, hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h276, h287, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p289_1, u2ehi4]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h0, h276, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p289_1, u2ehi4]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h277, hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h144, h281, hc01, hc24, hlam, hphi, ht12, p289_1]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h285, hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h276, h285, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p289_1, u2ehi4]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h278, hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h282, hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h286, hlam, p289_0]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [h287, hlam, p289_1]
                                · have p289_0 := h289c.1
                                  have p289_1 := h289c.2.1
                                  have p289_2 := h289c.2.2.1
                                  have p289_3 := h289c.2.2.2
                                  linarith only [hlam, p289_0]
                              · rcases h2bigk with h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c | h331c
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h0, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h0, h285, h287, h288, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h0, h287, h288, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  rcases p331_3 (m.d 0 2) (by simp) with h336 | h336
                                  · rcases p331_3 (m.d 1 2) (by simp) with h337 | h337
                                    · rcases p331_3 (m.d 2 3) (by simp) with h338 | h338
                                      · linarith only [h276, h338, hlam]
                                      · linarith only [h286, h338, hlam]
                                    · linarith only [h282, h337, hlam]
                                  · linarith only [h336, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h276, h285, h287, h288, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h285, h287, h288, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h287, h288, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  rcases p331_3 (m.d 0 2) (by simp) with h347 | h347
                                  · linarith only [h0, h347, hlam]
                                  · linarith only [h278, h347, hlam]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h276, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h281, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h276, h287, h288, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h0, h276, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p331_1, u2ehi4]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h277, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h144, h281, hc01, hc24, hlam, hphi, ht12, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h285, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h276, h285, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p331_1, u2ehi4]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h278, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h282, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h286, hlam, p331_0]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [h287, hlam, p331_1]
                                · have p331_0 := h331c.1
                                  have p331_1 := h331c.2.1
                                  have p331_2 := h331c.2.2.1
                                  have p331_3 := h331c.2.2.2
                                  linarith only [hlam, p331_0]
                            · linarith only [h287, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                          · linarith only [h286, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h367 | h367
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h368 | h368
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h369 | h369
                              · rcases h2bigk with h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h0, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  rcases p370_3 (m.d 0 2) (by simp) with h373 | h373
                                  · rcases p370_3 (m.d 1 2) (by simp) with h374 | h374
                                    · rcases p370_3 (m.d 2 3) (by simp) with h375 | h375
                                      · linarith only [h375, hlam, p370_0]
                                      · rcases p370_3 (m.d 2 4) (by simp) with h377 | h377
                                        · linarith only [h277, h377, hlam]
                                        · linarith only [h285, h377, hlam]
                                    · linarith only [h281, h374, hlam]
                                  · linarith only [h373, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  rcases p370_3 (m.d 0 2) (by simp) with h382 | h382
                                  · rcases p370_3 (m.d 1 2) (by simp) with h383 | h383
                                    · rcases p370_3 (m.d 2 3) (by simp) with h384 | h384
                                      · linarith only [h276, h384, hlam]
                                      · rcases p370_3 (m.d 2 4) (by simp) with h386 | h386
                                        · linarith only [h386, hlam, p370_0]
                                        · rcases p370_3 (m.d 2 5) (by simp) with h388 | h388
                                          · linarith only [h278, h388, hlam]
                                          · rcases h3bigk with h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [hlam, p390_0]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h144, hlam, p390_1]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              rcases p390_3 (m.d 0 3) (by simp) with h393 | h393
                                              · rcases p390_3 (m.d 1 3) (by simp) with h394 | h394
                                                · rcases p390_3 (m.d 2 3) (by simp) with h395 | h395
                                                  · linarith only [h276, h395, hlam]
                                                  · rcases p390_3 (m.d 3 4) (by simp) with h397 | h397
                                                    · linarith only [h279, h397, hlam]
                                                    · linarith only [h285, h397, hlam]
                                                · linarith only [h281, h394, hlam]
                                              · linarith only [h276, h393, hlam]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h285, h367, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p390_1, u2ehi4]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h279, h285, h367, hlam, p390_2]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h279, h285, h367, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p390_1, u2ehi4]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [hlam, p390_0]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              rcases p390_3 (m.d 0 3) (by simp) with h406 | h406
                                              · linarith only [h144, h406, hlam]
                                              · linarith only [h276, h406, hlam]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h281, h285, h367, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p390_1, u2ehi4]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h144, h279, h285, h367, hlam, p390_2]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h276, hlam, p390_1]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h281, hlam, p390_1]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [hlam, p390_0]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h285, hlam, p390_0]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h279, h285, hc03, hc35, hlam, hphi, ht0b, ht5b, p390_1]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h279, hlam, p390_0]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h283, hlam, p390_0]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h279, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p390_1, u2ehi2]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [hlam, p390_0]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              rcases p390_3 (m.d 0 3) (by simp) with h420 | h420
                                              · rcases p390_3 (m.d 1 3) (by simp) with h421 | h421
                                                · rcases p390_3 (m.d 2 3) (by simp) with h422 | h422
                                                  · linarith only [h285, h422, hlam]
                                                  · linarith only [h367, h422, hlam]
                                                · linarith only [h284, h421, hlam]
                                              · linarith only [h280, h420, hlam]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h280, hlam, p390_0]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h284, hlam, p390_0]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h367, hlam, p390_0]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [h369, hlam, p390_1]
                                            · have p390_0 := h390c.1
                                              have p390_1 := h390c.2.1
                                              have p390_2 := h390c.2.2.1
                                              have p390_3 := h390c.2.2.2
                                              linarith only [hlam, p390_0]
                                    · linarith only [h0, h383, hlam, p370_1]
                                  · linarith only [h382, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  rcases p370_3 (m.d 0 2) (by simp) with h434 | h434
                                  · rcases p370_3 (m.d 1 2) (by simp) with h435 | h435
                                    · rcases p370_3 (m.d 2 3) (by simp) with h436 | h436
                                      · linarith only [h276, h436, hlam]
                                      · linarith only [h367, h436, hlam]
                                    · linarith only [h282, h435, hlam]
                                  · linarith only [h434, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h276, h279, h285, h367, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p370_1, u2ehi4]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  rcases p370_3 (m.d 0 2) (by simp) with h443 | h443
                                  · linarith only [h0, h443, hlam]
                                  · linarith only [h276, h443, hlam]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  rcases p370_3 (m.d 0 2) (by simp) with h446 | h446
                                  · linarith only [h0, h446, hlam]
                                  · linarith only [h277, h446, hlam]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  rcases p370_3 (m.d 0 2) (by simp) with h449 | h449
                                  · linarith only [h0, h449, hlam]
                                  · linarith only [h278, h449, hlam]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h276, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h281, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h285, hlam, p370_1]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h276, h279, h285, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p370_1, u2ehi4]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h277, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h0, hc24, hlam, hphi, p370_1, u2ehi0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h0, h276, h279, h285, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p370_1, u2ehi2]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h0, h276, h279, h285, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p370_1, u2ehi4]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h278, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h282, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h367, hlam, p370_0]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [h368, hlam, p370_1]
                                · have p370_0 := h370c.1
                                  have p370_1 := h370c.2.1
                                  have p370_2 := h370c.2.2.1
                                  have p370_3 := h370c.2.2.2
                                  linarith only [hlam, p370_0]
                              · linarith only [h285, h369, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                            · linarith only [h285, h367, h368, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                          · linarith only [h367, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h144, h280, h284, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                    · linarith only [h144, h279, h283, hlam]
                  · linarith only [h0, h282, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
                · linarith only [h0, h276, h281, hlam]
              · linarith only [h276, h280, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h475 | h475
              · rcases m.htr 1 2 3 (by decide) (by decide) with h476 | h476
                · rcases m.htr 1 2 5 (by decide) (by decide) with h477 | h477
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h478 | h478
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h479 | h479
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h480 | h480
                        · linarith only [h276, h278, h279, h475, h480, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h482 | h482
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h483 | h483
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h484 | h484
                              · rcases h2bigk with h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c | h485c
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h0, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  rcases p485_3 (m.d 0 2) (by simp) with h488 | h488
                                  · rcases p485_3 (m.d 1 2) (by simp) with h489 | h489
                                    · rcases p485_3 (m.d 2 3) (by simp) with h490 | h490
                                      · linarith only [h490, hlam, p485_0]
                                      · rcases p485_3 (m.d 2 4) (by simp) with h492 | h492
                                        · linarith only [h277, h492, hlam]
                                        · linarith only [h480, h492, hlam]
                                    · linarith only [h476, h489, hlam]
                                  · linarith only [h488, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  rcases p485_3 (m.d 0 2) (by simp) with h497 | h497
                                  · rcases p485_3 (m.d 1 2) (by simp) with h498 | h498
                                    · rcases p485_3 (m.d 2 3) (by simp) with h499 | h499
                                      · linarith only [h276, h499, hlam]
                                      · rcases p485_3 (m.d 2 4) (by simp) with h501 | h501
                                        · linarith only [h501, hlam, p485_0]
                                        · rcases p485_3 (m.d 2 5) (by simp) with h503 | h503
                                          · linarith only [h278, h503, hlam]
                                          · rcases h3bigk with h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [hlam, p505_0]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h144, hlam, p505_1]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h279, h478, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p505_1]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h279, hlam, p505_0]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h279, h478, h484, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p505_1]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              rcases p505_3 (m.d 0 3) (by simp) with h511 | h511
                                              · linarith only [h144, h511, hlam]
                                              · rcases p505_3 (m.d 1 3) (by simp) with h513 | h513
                                                · rcases p505_3 (m.d 2 3) (by simp) with h514 | h514
                                                  · linarith only [h476, h514, hlam]
                                                  · rcases p505_3 (m.d 3 4) (by simp) with h516 | h516
                                                    · linarith only [h478, h516, hlam]
                                                    · linarith only [h279, h516, hlam]
                                                · linarith only [h144, h513, hlam]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [hlam, p505_0]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              rcases p505_3 (m.d 0 3) (by simp) with h521 | h521
                                              · linarith only [h144, h521, hlam]
                                              · linarith only [h276, h521, hlam]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h144, h279, h476, hc01, hc12, hlam, hphi, p505_1]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h279, h475, h478, hlam, p505_2]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h276, hlam, p505_1]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h476, hlam, p505_1]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [hlam, p505_0]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h480, hlam, p505_0]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h276, h279, h478, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p505_1]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h276, h478, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p505_1, u2ehi2]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h478, hlam, p505_0]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h476, h478, h482, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p505_1, u2ehi4]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [hlam, p505_0]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              rcases p505_3 (m.d 0 3) (by simp) with h535 | h535
                                              · linarith only [h279, h535, hlam]
                                              · linarith only [h475, h535, hlam]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h475, hlam, p505_0]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h479, hlam, p505_0]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h482, hlam, p505_0]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [h484, hlam, p505_1]
                                            · have p505_0 := h505c.1
                                              have p505_1 := h505c.2.1
                                              have p505_2 := h505c.2.2.1
                                              have p505_3 := h505c.2.2.2
                                              linarith only [hlam, p505_0]
                                    · linarith only [h0, h498, hlam, p485_1]
                                  · linarith only [h497, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  rcases p485_3 (m.d 0 2) (by simp) with h545 | h545
                                  · rcases p485_3 (m.d 1 2) (by simp) with h546 | h546
                                    · rcases p485_3 (m.d 2 3) (by simp) with h547 | h547
                                      · linarith only [h276, h547, hlam]
                                      · linarith only [h482, h547, hlam]
                                    · linarith only [h477, h546, hlam]
                                  · linarith only [h545, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h276, h482, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p485_1, u2ehi4]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  rcases p485_3 (m.d 0 2) (by simp) with h554 | h554
                                  · linarith only [h0, h554, hlam]
                                  · linarith only [h276, h554, hlam]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  rcases p485_3 (m.d 0 2) (by simp) with h557 | h557
                                  · linarith only [h0, h557, hlam]
                                  · linarith only [h277, h557, hlam]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  rcases p485_3 (m.d 0 2) (by simp) with h560 | h560
                                  · linarith only [h0, h560, hlam]
                                  · linarith only [h278, h560, hlam]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h276, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h476, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h480, hlam, p485_1]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h277, h480, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p485_1, u2ehi4]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h277, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h277, h279, h476, h478, hlam, p485_1]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h277, h279, h476, h478, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p485_1, u2ehi2]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h277, h279, h476, h478, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p485_1, u2ehi4]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h278, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h477, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h482, hlam, p485_0]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [h483, hlam, p485_1]
                                · have p485_0 := h485c.1
                                  have p485_1 := h485c.2.1
                                  have p485_2 := h485c.2.2.1
                                  have p485_3 := h485c.2.2.2
                                  linarith only [hlam, p485_0]
                              · linarith only [h279, h484, hc03, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h480, h482, h483, hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo4]
                          · linarith only [h482, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h279, h475, h479, hc13, hc34, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h582 | h582
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h583 | h583
                        · linarith only [h144, h478, h583, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h585 | h585
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h586 | h586
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h587 | h587
                              · rcases h2bigk with h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c | h588c
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h0, hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  rcases p588_3 (m.d 0 2) (by simp) with h591 | h591
                                  · rcases p588_3 (m.d 1 2) (by simp) with h592 | h592
                                    · rcases p588_3 (m.d 2 3) (by simp) with h593 | h593
                                      · linarith only [h593, hlam, p588_0]
                                      · rcases p588_3 (m.d 2 4) (by simp) with h595 | h595
                                        · linarith only [h277, h595, hlam]
                                        · linarith only [h583, h595, hlam]
                                    · linarith only [h476, h592, hlam]
                                  · linarith only [h591, hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  rcases p588_3 (m.d 0 2) (by simp) with h600 | h600
                                  · rcases p588_3 (m.d 1 2) (by simp) with h601 | h601
                                    · rcases p588_3 (m.d 2 3) (by simp) with h602 | h602
                                      · linarith only [h276, h602, hlam]
                                      · rcases p588_3 (m.d 2 4) (by simp) with h604 | h604
                                        · linarith only [h604, hlam, p588_0]
                                        · rcases p588_3 (m.d 2 5) (by simp) with h606 | h606
                                          · linarith only [h278, h606, hlam]
                                          · rcases h3bigk with h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [hlam, p608_0]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h144, hlam, p608_1]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h144, h478, h585, hc34, hlam, hphi, ht23, p608_1, u2ehi4]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h279, hlam, p608_0]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              rcases p608_3 (m.d 0 3) (by simp) with h613 | h613
                                              · rcases p608_3 (m.d 1 3) (by simp) with h614 | h614
                                                · rcases p608_3 (m.d 2 3) (by simp) with h615 | h615
                                                  · linarith only [h276, h615, hlam]
                                                  · linarith only [h585, h615, hlam]
                                                · linarith only [h582, h614, hlam]
                                              · linarith only [h613, hlam, p608_0]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h478, hc03, hc34, hlam, hphi, p608_1]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [hlam, p608_0]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h478, h585, hc34, hlam, hphi, ht23, p608_1, u2ehi4]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h478, hlam, p608_0]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              rcases p608_3 (m.d 0 3) (by simp) with h624 | h624
                                              · linarith only [h144, h624, hlam]
                                              · linarith only [h475, h624, hlam]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h276, hlam, p608_1]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h476, hlam, p608_1]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [hlam, p608_0]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h583, hlam, p608_0]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h0, h583, h587, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p588_1, p608_1]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h276, h585, hc34, hlam, hphi, ht23, p608_1, u2ehi4]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h0, h144, h583, h585, hc01, hc12, hc34, hlam, hphi, ht23, p588_1, p608_1, u2ehi4]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h585, hc34, hlam, hphi, ht23, p608_1, u2ehi4]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [hlam, p608_0]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              rcases p608_3 (m.d 0 3) (by simp) with h636 | h636
                                              · linarith only [h279, h636, hlam]
                                              · linarith only [h475, h636, hlam]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h475, hlam, p608_0]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h582, hlam, p608_0]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h585, hlam, p608_0]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [h587, hlam, p608_1]
                                            · have p608_0 := h608c.1
                                              have p608_1 := h608c.2.1
                                              have p608_2 := h608c.2.2.1
                                              have p608_3 := h608c.2.2.2
                                              linarith only [hlam, p608_0]
                                    · linarith only [h0, h601, hlam, p588_1]
                                  · linarith only [h600, hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  rcases p588_3 (m.d 0 2) (by simp) with h646 | h646
                                  · rcases p588_3 (m.d 1 2) (by simp) with h647 | h647
                                    · rcases p588_3 (m.d 2 3) (by simp) with h648 | h648
                                      · linarith only [h276, h648, hlam]
                                      · linarith only [h585, h648, hlam]
                                    · linarith only [h477, h647, hlam]
                                  · linarith only [h646, hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h276, h585, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p588_1, u2ehi4]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  rcases p588_3 (m.d 0 2) (by simp) with h655 | h655
                                  · linarith only [h0, h655, hlam]
                                  · linarith only [h276, h655, hlam]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  rcases p588_3 (m.d 0 2) (by simp) with h658 | h658
                                  · linarith only [h0, h658, hlam]
                                  · linarith only [h277, h658, hlam]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  rcases p588_3 (m.d 0 2) (by simp) with h661 | h661
                                  · linarith only [h0, h661, hlam]
                                  · linarith only [h278, h661, hlam]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h276, hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h476, hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h583, hlam, p588_1]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h277, h583, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p588_1, u2ehi4]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h277, hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h0, h277, hlam, p588_1]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h0, h277, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p588_1, u2ehi2]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h0, h277, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p588_1, u2ehi4]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h278, hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h477, hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h585, hlam, p588_0]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [h586, hlam, p588_1]
                                · have p588_0 := h588c.1
                                  have p588_1 := h588c.2.1
                                  have p588_2 := h588c.2.2.1
                                  have p588_3 := h588c.2.2.2
                                  linarith only [hlam, p588_0]
                              · linarith only [h144, h478, h587, hc03, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h586, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
                          · linarith only [h585, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                      · linarith only [h144, h582, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h477, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
                · linarith only [h0, h276, h476, hlam]
              · linarith only [h276, h475, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
          · linarith only [h276, h278, hc25, hlam, hphi, u2ehi2]
        · linarith only [h276, h277, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h688 | h688
        · linarith only [h276, h688, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h690 | h690
          · linarith only [h276, h690, hc23, hlam, hphi, u2ehi4]
          · linarith only [h690, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

end R2N4
