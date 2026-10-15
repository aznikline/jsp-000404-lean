import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_0_L_I_L_0_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h1emin := hb1.2.1
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h6, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h0, h10, h6, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, h3, h9, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                        · linarith only [h0, h15, h3, h5, h6, h9, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h15, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h6, h7, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                · linarith only [h0, h20, h3, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h22, h3, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h22, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
              · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                    · linarith only [h1, h28, h5, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                      · linarith only [h1, h25, h30, h5, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h32 | h32
                        · linarith only [h0, h25, h32, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h32, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h27, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h25, h26, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h25, h3, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h3, h4, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h39 | h39
          · rcases m.htr 0 3 4 (by decide) (by decide) with h40 | h40
            · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
              · linarith only [h3, h39, h41, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h48 | h48
                          · linarith only [h0, h43, h48, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h48, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h3, h47, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h3, h43, h46, hc24, hlam, hphi, u4elo3]
                    · linarith only [h40, h41, h43, h45, hc24, hlam, hphi, u4elo0]
                  · linarith only [h43, h44, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h3, h39, h43, hc12, hc23, hlam, hphi]
            · linarith only [h3, h39, h40, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h57 | h57
            · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
              · linarith only [h0, h3, h58, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                · linarith only [h0, h39, h60, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h62 | h62
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h66 | h66
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                            · linarith only [h1, h63, h67, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · linarith only [h0, h39, h62, h65, h67, hc34, hc35, hlam, hphi, u4elo2, u5elo4]
                          · linarith only [h0, h39, h62, h65, h66, hc35, hlam, hphi, u5elo4]
                        · linarith only [h39, h64, h65, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h3, h62, h64, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h1, h57, h58, h62, h63, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h62, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
              · linarith only [h0, h3, h75, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                · linarith only [h0, h39, h77, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                    · linarith only [h1, h57, h80, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h84 | h84
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h85 | h85
                            · rcases h1emin with h86 | h86 | h86 | h86 | h86
                              · rcases h2bigk with h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h3, h57, h79, h82, h83, h85, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p87_1, u4elo2]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h3, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h39, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h3, h57, h82, h83, h85, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p87_1, u4elo2]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h0, hlam, p87_1]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h75, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h77, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h0, h83, h85, hc45, hlam, hphi, ht01, ht0b, ht5b, p87_1, u1elo0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  rcases p87_3 (m.d 0 2) (by simp) with h98 | h98
                                  · linarith only [h98, hlam, p87_0]
                                  · rcases p87_3 (m.d 1 2) (by simp) with h100 | h100
                                    · linarith only [h100, h75, hlam]
                                    · rcases p87_3 (m.d 2 3) (by simp) with h102 | h102
                                      · rcases p87_3 (m.d 2 4) (by simp) with h103 | h103
                                        · linarith only [h103, h82, hlam]
                                        · linarith only [h103, h39, hlam]
                                      · linarith only [h102, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  rcases p87_3 (m.d 0 2) (by simp) with h107 | h107
                                  · linarith only [h107, h3, hlam]
                                  · linarith only [h0, h107, hlam]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h3, h57, h82, hc02, hc23, hlam, hphi, p87_1]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h0, h3, h57, h79, h82, hlam, p87_2]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h0, h79, h83, h85, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p87_1, u4elo2]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h79, h83, h85, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p87_1, u4elo2]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h82, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  rcases p87_3 (m.d 0 2) (by simp) with h117 | h117
                                  · linarith only [h117, h39, hlam]
                                  · linarith only [h0, h117, h79, hlam]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h0, h79, hlam, p87_1]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h79, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h83, hlam, p87_0]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [h84, hlam, p87_1]
                                · have p87_0 := h87c.1
                                  have p87_1 := h87c.2.1
                                  have p87_2 := h87c.2.2.1
                                  have p87_3 := h87c.2.2.2
                                  linarith only [hlam, p87_0]
                              · linarith only [h0, h3, h57, h82, h86, hc23, hlam, ht12]
                              · linarith only [h1, h86, hlam, u1elo0]
                              · linarith only [h2, h86, hlam, u1elo0]
                              · linarith only [h0, h3, h57, h79, h83, h85, h86, hc45, hlam, hphi, ht12, ht23, ht34, u4elo3, u5elo1]
                            · linarith only [h0, h3, h57, h79, h83, h85, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                          · linarith only [h0, h3, h57, h79, h82, h83, h84, hc35, hlam, hphi, u5elo4]
                        · linarith only [h3, h57, h82, h83, hc02, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h3, h79, h82, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                  · linarith only [h79, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h135 | h135
      · rcases m.htr 0 2 3 (by decide) (by decide) with h136 | h136
        · linarith only [h0, h1, h136, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h138 | h138
          · rcases m.htr 0 3 4 (by decide) (by decide) with h139 | h139
            · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
              · linarith only [h0, h1, h136, h140, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h142 | h142
                · linarith only [h0, h1, h142, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · linarith only [h0, h1, h138, h142, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
            · linarith only [h0, h1, h139, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h146 | h146
            · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
              · linarith only [h0, h136, h147, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
                · linarith only [h0, h1, h149, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h151 | h151
                  · linarith only [h1, h135, h149, h151, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · linarith only [h151, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h1, h135, h146, hc14, hlam, hphi, u4elo3]
      · linarith only [h0, h135, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h156 | h156
    · rcases m.htr 0 1 4 (by decide) (by decide) with h157 | h157
      · rcases m.htr 0 2 3 (by decide) (by decide) with h158 | h158
        · rcases m.htr 0 2 4 (by decide) (by decide) with h159 | h159
          · rcases m.htr 0 3 4 (by decide) (by decide) with h160 | h160
            · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
              · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
                · rcases m.htr 1 2 5 (by decide) (by decide) with h163 | h163
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h164 | h164
                    · linarith only [h0, h156, h164, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · linarith only [h0, h156, h160, h164, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · linarith only [h0, h163, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h156, h161, h162, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h156, h158, h161, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
              · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                · rcases m.htr 1 2 5 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                    · linarith only [h156, h160, h173, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                      · linarith only [h0, h156, h160, h170, h175, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
                        · linarith only [h0, h157, h170, h173, h177, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h177, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h172, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h156, h170, h171, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h158, h170, hlam]
          · linarith only [h0, h156, h159, hc13, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h156, h158, hlam]
      · linarith only [h156, h157, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h186 | h186
      · rcases m.htr 0 2 3 (by decide) (by decide) with h187 | h187
        · rcases m.htr 0 2 4 (by decide) (by decide) with h188 | h188
          · rcases m.htr 0 3 4 (by decide) (by decide) with h189 | h189
            · rcases m.htr 1 2 3 (by decide) (by decide) with h190 | h190
              · rcases m.htr 1 2 4 (by decide) (by decide) with h191 | h191
                · rcases m.htr 1 2 5 (by decide) (by decide) with h192 | h192
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h193 | h193
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h194 | h194
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h195 | h195
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h196 | h196
                          · linarith only [h156, h186, h190, h191, h196, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h196, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h194, h195, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h156, h186, h190, h193, h194, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h156, h193, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h156, h190, h192, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h156, h186, h190, h191, hc14, hlam, hphi, u4elo2]
              · linarith only [h0, h186, h187, h190, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h156, h186, h189, hc14, hlam, hphi, u4elo3]
          · linarith only [h0, h186, h188, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h207 | h207
          · rcases m.htr 0 3 4 (by decide) (by decide) with h208 | h208
            · rcases m.htr 1 2 3 (by decide) (by decide) with h209 | h209
              · linarith only [h0, h186, h187, h209, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
                · rcases m.htr 1 2 5 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h213 | h213
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h215 | h215
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h216 | h216
                          · linarith only [h0, h186, h211, h216, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h216, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h186, h209, h211, h214, h215, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h186, h209, h211, h214, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h186, h208, h209, h211, h213, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h186, h211, h212, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h0, h186, h211, hc14, hlam, hphi, u4elo2]
            · linarith only [h0, h186, h187, h208, hc14, hlam, hphi, u4elo3]
          · linarith only [h0, h186, h207, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h226 | h226
        · rcases m.htr 0 2 4 (by decide) (by decide) with h227 | h227
          · rcases m.htr 0 3 4 (by decide) (by decide) with h228 | h228
            · rcases m.htr 1 2 3 (by decide) (by decide) with h229 | h229
              · rcases m.htr 1 2 4 (by decide) (by decide) with h230 | h230
                · rcases m.htr 1 2 5 (by decide) (by decide) with h231 | h231
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h234 | h234
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h235 | h235
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h236 | h236
                            · linarith only [h0, h226, h233, h236, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h236, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h235, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h233, h234, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                        · linarith only [h156, h228, h229, h233, h241, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h241, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h156, h228, h232, hlam]
                  · linarith only [h0, h231, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h156, h229, h230, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h226, h229, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h248 | h248
              · rcases m.htr 1 2 4 (by decide) (by decide) with h249 | h249
                · rcases m.htr 1 2 5 (by decide) (by decide) with h250 | h250
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h251 | h251
                    · linarith only [h156, h228, h248, h251, hc01, hlam, hphi, u1elo1]
                    · linarith only [h156, h251, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                  · linarith only [h0, h250, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h156, h248, h249, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h226, h248, hlam]
          · linarith only [h226, h227, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h258 | h258
          · rcases m.htr 0 3 4 (by decide) (by decide) with h259 | h259
            · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
              · linarith only [h226, h258, h260, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h262 | h262
                · rcases m.htr 1 2 5 (by decide) (by decide) with h263 | h263
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h265 | h265
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h266 | h266
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h267 | h267
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h268 | h268
                            · rcases h1emin with h269 | h269 | h269 | h269 | h269
                              · linarith only [h186, h269, hlam, u1elo3]
                              · rcases h2bigk with h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h0, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h226, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h0, h265, h268, hc45, hlam, hphi, ht01, ht0b, ht5b, p271_1, u1elo1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  rcases p271_3 (m.d 0 2) (by simp) with h276 | h276
                                  · rcases p271_3 (m.d 1 2) (by simp) with h277 | h277
                                    · rcases p271_3 (m.d 2 3) (by simp) with h278 | h278
                                      · rcases p271_3 (m.d 2 4) (by simp) with h279 | h279
                                        · linarith only [h258, h279, hlam]
                                        · linarith only [h267, h279, hlam]
                                      · linarith only [h266, h278, hlam]
                                    · linarith only [h263, h277, hlam]
                                  · linarith only [h276, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h260, hc02, hc23, hlam, hphi, p271_1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h260, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h260, h265, h268, hc45, hlam, hphi, ht01, ht0b, ht5b, p271_1, u1elo2]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  rcases p271_3 (m.d 0 2) (by simp) with h289 | h289
                                  · linarith only [h0, h289, hlam]
                                  · linarith only [h258, h265, h268, h289, hc45, hlam, hphi, u5elo2]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h258, h265, h268, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p271_1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h269, hc23, hlam, ht12, p271_1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  rcases p271_3 (m.d 0 2) (by simp) with h295 | h295
                                  · linarith only [h226, h295, hlam]
                                  · linarith only [h258, h295, hlam]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  rcases p271_3 (m.d 0 2) (by simp) with h298 | h298
                                  · linarith only [h226, h298, hlam]
                                  · linarith only [h258, h263, h265, h268, h298, hc45, hlam, hphi, u5elo1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h258, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h262, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h265, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h0, h258, hc25, hlam, hphi, ht01, ht0b, ht5b, p271_1, u1elo1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p271_1, u5elo2]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h263, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h266, hlam, p271_0]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [h267, hlam, p271_1]
                                · have p271_0 := h271c.1
                                  have p271_1 := h271c.2.1
                                  have p271_2 := h271c.2.2.1
                                  have p271_3 := h271c.2.2.2
                                  linarith only [hlam, p271_0]
                              · rcases h2bigk with h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h0, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h226, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h0, h260, h265, h268, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p311_1]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  rcases p311_3 (m.d 0 2) (by simp) with h316 | h316
                                  · rcases p311_3 (m.d 1 2) (by simp) with h317 | h317
                                    · rcases p311_3 (m.d 2 3) (by simp) with h318 | h318
                                      · rcases p311_3 (m.d 2 4) (by simp) with h319 | h319
                                        · linarith only [h258, h319, hlam]
                                        · linarith only [h267, h319, hlam]
                                      · linarith only [h266, h318, hlam]
                                    · linarith only [h263, h317, hlam]
                                  · linarith only [h316, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h260, hc02, hc23, hlam, hphi, p311_1]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h260, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h260, h265, h268, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p311_1]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  rcases p311_3 (m.d 0 2) (by simp) with h329 | h329
                                  · linarith only [h0, h329, hlam]
                                  · linarith only [h258, h265, h268, h329, hc45, hlam, hphi, u5elo2]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h258, h265, h268, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p311_1]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p311_1]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  rcases p311_3 (m.d 0 2) (by simp) with h335 | h335
                                  · linarith only [h226, h335, hlam]
                                  · linarith only [h258, h335, hlam]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  rcases p311_3 (m.d 0 2) (by simp) with h338 | h338
                                  · linarith only [h226, h338, hlam]
                                  · linarith only [h258, h263, h265, h268, h338, hc45, hlam, hphi, u5elo1]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h258, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h262, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h265, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h0, h258, hc25, hlam, hphi, ht01, ht0b, ht5b, p311_1, u1elo1]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p311_1, u5elo2]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h263, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h266, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h267, hlam, p311_1]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [hlam, p311_0]
                              · rcases h2bigk with h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h0, hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h226, hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h0, h260, h265, h268, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p351_1]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  rcases p351_3 (m.d 0 2) (by simp) with h356 | h356
                                  · rcases p351_3 (m.d 1 2) (by simp) with h357 | h357
                                    · rcases p351_3 (m.d 2 3) (by simp) with h358 | h358
                                      · rcases p351_3 (m.d 2 4) (by simp) with h359 | h359
                                        · linarith only [h258, h359, hlam]
                                        · linarith only [h267, h359, hlam]
                                      · linarith only [h266, h358, hlam]
                                    · linarith only [h263, h357, hlam]
                                  · linarith only [h356, hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h260, hc02, hc23, hlam, hphi, p351_1]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h260, hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h260, h265, h268, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p351_1]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  rcases p351_3 (m.d 0 2) (by simp) with h369 | h369
                                  · linarith only [h0, h369, hlam]
                                  · linarith only [h258, h265, h268, h369, hc45, hlam, hphi, u5elo2]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h258, h265, h268, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p351_1]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p351_1]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  rcases p351_3 (m.d 0 2) (by simp) with h375 | h375
                                  · linarith only [h226, h375, hlam]
                                  · linarith only [h258, h375, hlam]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  rcases p351_3 (m.d 0 2) (by simp) with h378 | h378
                                  · linarith only [h226, h378, hlam]
                                  · linarith only [h258, h263, h265, h268, h378, hc45, hlam, hphi, u5elo1]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h258, hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h262, hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h265, hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h0, h258, hc25, hlam, hphi, ht01, ht0b, ht5b, p351_1, u1elo1]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p351_1, u5elo2]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h263, hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h266, hlam, p351_0]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [h267, hlam, p351_1]
                                · have p351_0 := h351c.1
                                  have p351_1 := h351c.2.1
                                  have p351_2 := h351c.2.2.1
                                  have p351_3 := h351c.2.2.2
                                  linarith only [hlam, p351_0]
                              · linarith only [h269, hlam, ht12, ht23, ht34, ht45, u5elo1]
                            · linarith only [h268, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h265, h267, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h260, h266, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h186, h260, h262, h265, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h156, h259, h264, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
                  · linarith only [h186, h262, h263, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h262, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h226, h258, h259, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h400 | h400
            · rcases m.htr 1 2 3 (by decide) (by decide) with h401 | h401
              · linarith only [h0, h226, h401, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h403 | h403
                · linarith only [h0, h258, h403, hc01, hlam, hphi, u1elo1]
                · linarith only [h0, h403, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
              · linarith only [h0, h226, h406, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h408 | h408
                · linarith only [h0, h258, h406, h408, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h408, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

theorem r1l7_11_12_14_25_L_0_L_I_L_0_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h1elo := hb1.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h2, h6, h9, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h1, h9, hc34, hlam, hphi, u4elo0]
                  · linarith only [h1, h8, hc24, hlam, hphi, u4elo0]
                · linarith only [h6, h7, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                    · rcases h5bigk with h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c | h17c
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hc15, hlam, hphi, p17_1, u5elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hc25, hlam, hphi, p17_1, u5elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h16, hc45, hlam, hphi, p17_1, u5elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hc45, hlam, hphi, p17_1, u5elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hc05, hlam, hphi, p17_1, u5elo1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h14, h16, hc45, hlam, hphi, p17_1, u5elo1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h16, hc45, hlam, hphi, p17_1, u5elo1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hc45, hlam, hphi, p17_1, u5elo1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h0, hlam, p17_1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h4, hlam, p17_1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h0, h16, hc45, hlam, hphi, p17_1, u5elo0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h14, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p17_1, u4elo3]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hc05, hlam, hphi, p17_1, u5elo3]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h14, h6, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p17_1, u4elo3]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h14, hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h14, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p17_1, u4elo3]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h1, hlam, p17_1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h5, hlam, p17_1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h15, hlam, p17_1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [h16, hlam, p17_1]
                      · have p17_0 := h17c.1
                        have p17_1 := h17c.2.1
                        have p17_2 := h17c.2.2.1
                        have p17_3 := h17c.2.2.2
                        linarith only [hlam, p17_0]
                    · linarith only [h16, h6, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h1, h14, h15, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h45 | h45
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h46 | h46
                    · rcases h5bigk with h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hc15, hlam, hphi, p47_1, u5elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h14, hc23, hlam, hphi, ht34, ht45, p47_1, u5elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h14, hc23, hlam, hphi, ht34, ht45, p47_1, u5elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hc45, hlam, hphi, p47_1, u5elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hc05, hlam, hphi, p47_1, u5elo1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h14, hc23, hlam, hphi, ht34, ht45, p47_1, u5elo1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h14, hc23, hlam, hphi, ht34, ht45, p47_1, u5elo1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hc45, hlam, hphi, p47_1, u5elo1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h0, hlam, p47_1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h4, hlam, p47_1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h14, hlam, p47_1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h0, hc45, hlam, hphi, p47_1, u5elo0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hc05, hlam, hphi, p47_1, u5elo3]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hc15, hlam, hphi, p47_1, u5elo3]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hc25, hlam, hphi, p47_1, u5elo3]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hlam, p47_0]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [hc45, hlam, hphi, p47_1, u5elo3]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h1, hlam, p47_1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h5, hlam, p47_1]
                      · have p47_0 := h47c.1
                        have p47_1 := h47c.2.1
                        have p47_2 := h47c.2.2.1
                        have p47_3 := h47c.2.2.2
                        linarith only [h45, hlam, p47_1]
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
                    · linarith only [h1, h46, hc34, hlam, hphi, u4elo0]
                  · linarith only [h1, h45, hc24, hlam, hphi, u4elo0]
            · linarith only [h1, h5, hc14, hlam, hphi, u4elo0]
          · linarith only [h0, h2, h4, hc23, hlam, hphi, ht34, ht45, u5elo0]
        · linarith only [h2, h3, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
        · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
          · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
            · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
              · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                · rcases m.htr 2 4 5 (by decide) (by decide) with h83 | h83
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h84 | h84
                    · rcases h5bigk with h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [hlam, p85_0]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [hc15, hlam, hphi, p85_1, u5elo0]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [hc25, hlam, hphi, p85_1, u5elo0]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h84, hc45, hlam, hphi, p85_1, u5elo0]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [hc45, hlam, hphi, p85_1, u5elo0]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [hc05, hlam, hphi, p85_1, u5elo1]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [hlam, p85_0]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h82, h84, hc45, hlam, hphi, p85_1, u5elo1]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h84, hc45, hlam, hphi, p85_1, u5elo1]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [hc45, hlam, hphi, p85_1, u5elo1]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h0, hlam, p85_1]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h79, hlam, p85_1]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [hlam, p85_0]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h0, h84, hc45, hlam, hphi, p85_1, u5elo0]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h78, h83, hc45, hlam, hphi, ht01, ht0b, ht5b, p85_1, u1elo1]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [hc05, hlam, hphi, p85_1, u5elo3]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h2, h78, h82, h83, hc15, hlam, hphi, ht01, ht0b, ht5b, p85_1, u1elo2]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h82, hlam, p85_0]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [hlam, p85_0]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h2, h78, h82, h83, hc45, hlam, hphi, ht01, ht0b, ht5b, p85_1, u1elo2]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h1, hlam, p85_1]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h80, hlam, p85_1]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h83, hlam, p85_1]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [h84, hlam, p85_1]
                      · have p85_0 := h85c.1
                        have p85_1 := h85c.2.1
                        have p85_2 := h85c.2.2.1
                        have p85_3 := h85c.2.2.2
                        linarith only [hlam, p85_0]
                    · linarith only [h1, h84, hc34, hlam, hphi, u4elo0]
                  · linarith only [h1, h83, hc24, hlam, hphi, u4elo0]
                · linarith only [h2, h82, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h2, h78, h81, hc24, hlam, hphi, u4elo3]
            · linarith only [h1, h80, hc14, hlam, hphi, u4elo0]
          · linarith only [h78, h79, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
          · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
            · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
              · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                    · rcases h5bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h117, h120, h122, hc45, hlam, hphi, p123_1, u5elo0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h120, h122, hc45, hlam, hphi, p123_1, u5elo0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h122, hc45, hlam, hphi, p123_1, u5elo0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hc45, hlam, hphi, p123_1, u5elo0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hc05, hlam, hphi, p123_1, u5elo1]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h117, h120, h122, h78, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p123_1, u4elo2]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h117, h122, h78, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p123_1, u4elo2]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h117, h78, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p123_1, u4elo2]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h0, hlam, p123_1]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h117, hlam, p123_1]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h0, h122, hc45, hlam, hphi, p123_1, u5elo0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h117, h78, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p123_1, u4elo2]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hc05, hlam, hphi, p123_1, u5elo3]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h117, h120, h78, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p123_1, u4elo2]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h120, hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [hlam, p123_0]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h117, h120, h78, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p123_1, u4elo2]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h1, hlam, p123_1]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h118, hlam, p123_1]
                      · have p123_0 := h123c.1
                        have p123_1 := h123c.2.1
                        have p123_2 := h123c.2.2.1
                        have p123_3 := h123c.2.2.2
                        linarith only [h121, hlam, p123_1]
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
                    · linarith only [h1, h122, hc34, hlam, hphi, u4elo0]
                  · linarith only [h118, h121, h78, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h119, h120, h78, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h117, h119, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
            · linarith only [h1, h118, hc14, hlam, hphi, u4elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
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
                        linarith only [h117, hc12, hlam, hphi, ht23, ht34, ht45, p159_1, u5elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h117, hc12, hlam, hphi, ht23, ht34, ht45, p159_1, u5elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [hc35, hlam, hphi, p159_1, u5elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [hc45, hlam, hphi, p159_1, u5elo0]
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
                        linarith only [h117, hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h0, h117, h158, hc45, hlam, hphi, p159_1, u5elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h0, h117, hc45, hlam, hphi, p159_1, u5elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h0, hlam, p159_1]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h0, hc15, hlam, hphi, p159_1, u5elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [hlam, p159_0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h0, h158, hc45, hlam, hphi, p159_1, u5elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h0, hc45, hlam, hphi, p159_1, u5elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [hc05, hlam, hphi, p159_1, u5elo3]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h117, h155, h158, hc12, hc23, hlam, hphi, p159_1]
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
                        linarith only [h0, h156, hc45, hlam, hphi, p159_1, u5elo0]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h1, hlam, p159_1]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h154, hlam, p159_1]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h157, hlam, p159_1]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [h158, hlam, p159_1]
                      · have p159_0 := h159c.1
                        have p159_1 := h159c.2.1
                        have p159_2 := h159c.2.2.1
                        have p159_3 := h159c.2.2.2
                        linarith only [hlam, p159_0]
                    · linarith only [h154, h158, hc34, hlam, hphi, u4elo1]
                  · linarith only [h154, h157, h78, hlam]
                · linarith only [h156, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h155, h2, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · linarith only [h1, h154, hc14, hlam, hphi, u4elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h190 | h190
      · rcases m.htr 1 2 4 (by decide) (by decide) with h191 | h191
        · rcases m.htr 1 2 5 (by decide) (by decide) with h192 | h192
          · rcases m.htr 1 4 5 (by decide) (by decide) with h193 | h193
            · linarith only [h1, h193, hc04, hlam, hphi, u4elo1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
              · rcases m.htr 2 3 5 (by decide) (by decide) with h196 | h196
                · rcases m.htr 2 4 5 (by decide) (by decide) with h197 | h197
                  · linarith only [h191, h193, h197, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h199 | h199
                    · linarith only [h191, h193, h195, h199, hlam]
                    · rcases h5bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [hlam, p201_0]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h192, hc25, hlam, hphi, p201_1, u5elo0]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h1, hc25, hlam, hphi, p201_1, u5elo4]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h1, h199, hc34, hlam, hphi, ht45, p201_1, u5elo4]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h1, hlam, p201_0]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [hc05, hlam, hphi, p201_1, u5elo1]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [hlam, p201_0]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h195, h197, hc34, hlam, hphi, ht45, p201_1, u5elo1]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h193, h199, hc34, hlam, hphi, ht45, p201_1, u5elo4]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h193, hlam, p201_0]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h0, hlam, p201_1]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h192, hlam, p201_1]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [hlam, p201_0]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h0, h199, hc34, hlam, hphi, ht45, p201_1, u5elo0]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h197, hlam, p201_0]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [hc05, hlam, hphi, p201_1, u5elo3]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h190, h196, hc15, hlam, hphi, ht01, ht0b, ht5b, p201_1, u1elo1]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h196, hlam, p201_0]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [hlam, p201_0]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h199, hlam, p201_0]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [hc05, hlam, hphi, p201_1, u5elo4]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h192, hc25, hlam, hphi, p201_1, u5elo4]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [h196, hc35, hlam, hphi, p201_1, u5elo4]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [hc35, hlam, hphi, p201_1, u5elo4]
                      · have p201_0 := h201c.1
                        have p201_1 := h201c.2.1
                        have p201_2 := h201c.2.2.1
                        have p201_3 := h201c.2.2.2
                        linarith only [hlam, p201_0]
                · linarith only [h195, h196, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h228 | h228
                · linarith only [h191, h193, h195, h228, hc35, hlam, hphi, u5elo4]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h230 | h230
                  · linarith only [h191, h193, h230, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h232 | h232
                    · linarith only [h193, h232, hc14, hlam, hphi, u4elo3]
                    · linarith only [h195, h232, hc23, hlam, hphi, ht34, u4elo4]
          · linarith only [h0, h1, h190, h192, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h190, h191, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h237 | h237
        · rcases m.htr 1 2 5 (by decide) (by decide) with h238 | h238
          · rcases m.htr 1 4 5 (by decide) (by decide) with h239 | h239
            · linarith only [h1, h239, hc04, hlam, hphi, u4elo1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h241 | h241
              · rcases m.htr 2 3 5 (by decide) (by decide) with h242 | h242
                · rcases m.htr 2 4 5 (by decide) (by decide) with h243 | h243
                  · linarith only [h237, h239, h243, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h245 | h245
                    · linarith only [h237, h239, h241, h245, hlam]
                    · rcases h5bigk with h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [hlam, p247_0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [hc15, hlam, hphi, p247_1, u5elo0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h241, h243, hc34, hlam, hphi, ht45, p247_1, u5elo0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [hc35, hlam, hphi, p247_1, u5elo0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h1, hlam, p247_0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [hc05, hlam, hphi, p247_1, u5elo1]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [hlam, p247_0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h243, hc24, hlam, hphi, ht45, p247_1, u5elo1]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h245, hc34, hlam, hphi, ht45, p247_1, u5elo1]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h239, hlam, p247_0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h0, hlam, p247_1]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h238, hlam, p247_1]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [hlam, p247_0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h0, h245, hc34, hlam, hphi, ht45, p247_1, u5elo0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h243, hlam, p247_0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [hc05, hlam, hphi, p247_1, u5elo3]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h190, h238, h242, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p247_1]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h242, hlam, p247_0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [hlam, p247_0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h245, hlam, p247_0]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [hc05, hlam, hphi, p247_1, u5elo4]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h238, h242, hc35, hlam, hphi, p247_1, u5elo4]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [h242, hc35, hlam, hphi, p247_1, u5elo4]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [hc35, hlam, hphi, p247_1, u5elo4]
                      · have p247_0 := h247c.1
                        have p247_1 := h247c.2.1
                        have p247_2 := h247c.2.2.1
                        have p247_3 := h247c.2.2.2
                        linarith only [hlam, p247_0]
                · linarith only [h190, h242, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h190, h241, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h237, h238, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h276 | h276
          · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
            · linarith only [h1, h277, hc04, hlam, hphi, u4elo1]
            · linarith only [h237, h276, h277, hc25, hlam, hphi, u5elo4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h280 | h280
            · linarith only [h0, h1, h276, h280, hc12, hlam, hphi, ht23, ht34, u4elo1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h282 | h282
              · rcases m.htr 2 3 5 (by decide) (by decide) with h283 | h283
                · rcases m.htr 2 4 5 (by decide) (by decide) with h284 | h284
                  · linarith only [h0, h1, h276, h284, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h237, h284, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h237, h282, h283, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h190, h282, hc12, hlam, hphi, ht23, ht34, u4elo3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h289 | h289
    · rcases m.htr 1 2 3 (by decide) (by decide) with h290 | h290
      · rcases m.htr 1 2 4 (by decide) (by decide) with h291 | h291
        · rcases m.htr 1 2 5 (by decide) (by decide) with h292 | h292
          · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
            · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
              · rcases m.htr 2 3 5 (by decide) (by decide) with h295 | h295
                · rcases m.htr 2 4 5 (by decide) (by decide) with h296 | h296
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h297 | h297
                    · linarith only [h290, h294, h297, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h289, h297, hc34, hlam, hphi, u4elo0]
                  · linarith only [h289, h296, hc24, hlam, hphi, u4elo0]
                · linarith only [h294, h295, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h302 | h302
                · linarith only [h0, h294, h302, hc02, hlam, hphi, ht23, ht34, u4elo3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h304 | h304
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h305 | h305
                    · rcases h5bigk with h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h0, h292, hc02, hlam, hphi, ht23, ht34, ht45, p306_1, u5elo0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h0, hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h0, h292, h302, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p306_1, u1elo4]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h0, h292, hc45, hlam, hphi, p306_1, u5elo1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hc05, hlam, hphi, p306_1, u5elo1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hc25, hlam, hphi, p306_1, u5elo1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h0, h302, hc02, hlam, hphi, ht23, ht34, ht45, p306_1, u5elo1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hc45, hlam, hphi, p306_1, u5elo1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p306_1, u5elo2]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h292, hlam, p306_1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h302, hlam, p306_1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h291, h304, hc45, hlam, hphi, ht01, ht0b, ht5b, p306_1, u1elo1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p306_1, u5elo3]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hc15, hlam, hphi, p306_1, u5elo3]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hc25, hlam, hphi, p306_1, u5elo3]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hc45, hlam, hphi, p306_1, u5elo3]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h289, hlam, p306_1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h293, hlam, p306_1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h304, hlam, p306_1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h305, hlam, p306_1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hlam, p306_0]
                    · linarith only [h289, h305, hc34, hlam, hphi, u4elo0]
                  · linarith only [h289, h304, hc24, hlam, hphi, u4elo0]
            · linarith only [h289, h293, hc14, hlam, hphi, u4elo0]
          · linarith only [h290, h292, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · linarith only [h290, h291, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h337 | h337
        · rcases m.htr 1 2 5 (by decide) (by decide) with h338 | h338
          · linarith only [h0, h290, h338, hc02, hc23, hlam, hphi]
          · linarith only [h337, h338, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h341 | h341
          · linarith only [h0, h337, h341, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h343 | h343
            · rcases m.htr 2 3 4 (by decide) (by decide) with h344 | h344
              · rcases m.htr 2 3 5 (by decide) (by decide) with h345 | h345
                · rcases m.htr 2 4 5 (by decide) (by decide) with h346 | h346
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h347 | h347
                    · rcases h5bigk with h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c | h348c
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [hlam, p348_0]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [hc15, hlam, hphi, p348_1, u5elo0]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h0, hlam, p348_0]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h0, hc35, hlam, hphi, p348_1, u5elo2]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h0, hc45, hlam, hphi, p348_1, u5elo2]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [hc05, hlam, hphi, p348_1, u5elo1]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [hlam, p348_0]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h341, hlam, p348_0]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h341, h347, hc45, hlam, hphi, p348_1, u5elo2]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h341, hc45, hlam, hphi, p348_1, u5elo2]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p348_1, u5elo2]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [hc15, hlam, hphi, p348_1, u5elo2]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [hlam, p348_0]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h347, hc45, hlam, hphi, p348_1, u5elo2]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [hc45, hlam, hphi, p348_1, u5elo2]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p348_1, u5elo3]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h341, h345, hc12, hlam, hphi, ht23, ht34, ht45, p348_1, u5elo2]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h345, hlam, p348_0]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [hlam, p348_0]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h345, hc45, hlam, hphi, p348_1, u5elo2]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h289, hlam, p348_1]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h343, hlam, p348_1]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h346, hlam, p348_1]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [h347, hlam, p348_1]
                      · have p348_0 := h348c.1
                        have p348_1 := h348c.2.1
                        have p348_2 := h348c.2.2.1
                        have p348_3 := h348c.2.2.2
                        linarith only [hlam, p348_0]
                    · linarith only [h289, h347, hc34, hlam, hphi, u4elo0]
                  · linarith only [h289, h337, h346, hc14, hlam, hphi, u4elo0]
                · linarith only [h290, h345, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h290, h344, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · linarith only [h289, h343, hc14, hlam, hphi, u4elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h379 | h379
      · rcases m.htr 1 2 4 (by decide) (by decide) with h380 | h380
        · rcases m.htr 1 2 5 (by decide) (by decide) with h381 | h381
          · rcases m.htr 1 4 5 (by decide) (by decide) with h382 | h382
            · linarith only [h289, h382, hc04, hlam, hphi, u4elo1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h384 | h384
              · rcases m.htr 2 3 5 (by decide) (by decide) with h385 | h385
                · rcases m.htr 2 4 5 (by decide) (by decide) with h386 | h386
                  · linarith only [h0, h380, h381, h382, h386, hc02, hlam, hphi, ht23, ht34, u4elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h388 | h388
                    · linarith only [h0, h381, h382, h388, hc02, hlam, hphi, ht23, ht34, u4elo3]
                    · rcases h5bigk with h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c | h390c
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h0, h381, hlam, p390_1]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h0, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hc35, hlam, hphi, p390_1, u5elo0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h289, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h382, hc05, hlam, hphi, p390_1, u5elo4]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h0, h382, hc02, hlam, hphi, ht23, ht34, ht45, p390_1, u5elo4]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h382, h388, hc34, hlam, hphi, ht45, p390_1, u5elo4]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h382, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h0, h379, h385, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p390_1, u1elo1]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h381, hlam, p390_1]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h379, h385, h388, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p390_1, u1elo1]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h386, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p390_1, u5elo3]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h379, h385, hc15, hlam, hphi, ht01, ht0b, ht5b, p390_1, u1elo1]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h385, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h388, hlam, p390_0]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p390_1, u5elo4]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hc15, hlam, hphi, p390_1, u5elo4]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [h0, hc02, hlam, hphi, ht23, ht34, ht45, p390_1, u5elo4]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hc35, hlam, hphi, p390_1, u5elo4]
                      · have p390_0 := h390c.1
                        have p390_1 := h390c.2.1
                        have p390_2 := h390c.2.2.1
                        have p390_3 := h390c.2.2.2
                        linarith only [hlam, p390_0]
                · linarith only [h384, h385, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h417 | h417
                · linarith only [h380, h382, h384, h417, hc35, hlam, hphi, u5elo4]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h419 | h419
                  · linarith only [h380, h382, h419, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h421 | h421
                    · linarith only [h382, h421, hc14, hlam, hphi, u4elo3]
                    · linarith only [h384, h421, hc23, hlam, hphi, ht34, u4elo4]
          · linarith only [h379, h381, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · linarith only [h379, h380, hc23, hlam, hphi, ht34, u4elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h426 | h426
        · rcases m.htr 1 2 5 (by decide) (by decide) with h427 | h427
          · linarith only [h0, h379, h427, hc02, hc23, hlam, hphi]
          · linarith only [h426, h427, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h430 | h430
          · linarith only [h0, h426, h430, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h432 | h432
            · linarith only [h289, h426, h432, hc04, hlam, hphi, u4elo2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h434 | h434
              · rcases m.htr 2 3 5 (by decide) (by decide) with h435 | h435
                · rcases m.htr 2 4 5 (by decide) (by decide) with h436 | h436
                  · linarith only [h426, h432, h436, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h426, h436, hc12, hlam, hphi, ht23, ht34, u4elo4]
                · linarith only [h379, h435, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h379, h434, hc12, hlam, hphi, ht23, ht34, u4elo3]

end R2N4
