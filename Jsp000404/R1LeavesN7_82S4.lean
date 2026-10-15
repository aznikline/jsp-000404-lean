import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_13_25_L_0_L_I_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h6, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h0, h10, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h9, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h0, h14, h3, h4, h8, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h14, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h18, h3, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · linarith only [h18, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h5, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h22 | h22
            · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
              · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
                · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
                  · linarith only [h22, h25, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h27 | h27
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                      · linarith only [h0, h1, h27, h28, h3, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                        · linarith only [h0, h23, h30, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h1, h27, h30, h4, hc23, hc34, hlam, hphi]
                    · linarith only [h22, h27, hc13, hlam, hphi, ht34, ht45, u5elo0]
                · linarith only [h24, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
                · linarith only [h0, h23, h3, h35, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · linarith only [h35, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h22, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h39 | h39
          · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
            · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
              · linarith only [h0, h3, h41, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
                          · linarith only [h1, h44, h48, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h48, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h3, h47, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h3, h43, h44, h46, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                    · linarith only [h45, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h1, h39, h41, h43, h44, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · linarith only [h43, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h40, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h57 | h57
            · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
              · linarith only [h0, h3, h58, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
                · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                  · linarith only [h1, h39, h61, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h66 | h66
                          · rcases h3bigk with h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h39, h58, h60, h64, h65, h66, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p67_1]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h3, hlam, p67_1]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h39, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h39, h64, h66, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p67_1]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h1, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h58, hlam, p67_1]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h61, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h1, h66, hc45, hlam, hphi, ht01, ht0b, ht5b, p67_1, u1elo0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              rcases p67_3 (m.d 0 3) (by simp) with h78 | h78
                              · linarith only [h3, h78, hlam]
                              · rcases p67_3 (m.d 1 3) (by simp) with h80 | h80
                                · linarith only [h58, h80, hlam]
                                · rcases p67_3 (m.d 2 3) (by simp) with h82 | h82
                                  · rcases p67_3 (m.d 3 4) (by simp) with h83 | h83
                                    · linarith only [h64, h83, hlam]
                                    · linarith only [h39, h83, hlam]
                                  · linarith only [h3, h82, hlam]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              rcases p67_3 (m.d 0 3) (by simp) with h87 | h87
                              · linarith only [h3, h87, hlam]
                              · linarith only [h1, h87, hlam]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h0, h3, h39, h60, h65, h66, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p67_1]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h0, h3, h39, h60, h64, h65, hlam, p67_2]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h0, h3, h60, h64, h65, h66, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p67_1]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h58, h60, h64, h65, h66, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p67_1]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h64, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              rcases p67_3 (m.d 0 3) (by simp) with h97 | h97
                              · linarith only [h39, h97, hlam]
                              · linarith only [h57, h97, hlam]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h57, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h63, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h65, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [h66, hlam, p67_0]
                            · have p67_0 := h67c.1
                              have p67_1 := h67c.2.1
                              have p67_2 := h67c.2.2.1
                              have p67_3 := h67c.2.2.2
                              linarith only [hlam, p67_0]
                          · linarith only [h66, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h65, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h108 | h108
                          · rcases h3bigk with h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h1, h107, h108, h58, h60, hc45, hlam, hphi, ht01, ht0b, ht5b, p109_1, u1elo0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h3, hlam, p109_1]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h39, hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              rcases p109_3 (m.d 0 3) (by simp) with h114 | h114
                              · rcases p109_3 (m.d 1 3) (by simp) with h115 | h115
                                · linarith only [h1, h115, hlam]
                                · linarith only [h115, h63, hlam]
                              · linarith only [h114, hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h1, hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h58, hlam, p109_1]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h61, hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h1, h108, hc45, hlam, hphi, ht01, ht0b, ht5b, p109_1, u1elo0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h64, hc03, hc34, hlam, hphi, p109_1]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h64, hc13, hc34, hlam, hphi, p109_1]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h64, hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              rcases p109_3 (m.d 0 3) (by simp) with h128 | h128
                              · linarith only [h128, h3, hlam]
                              · linarith only [h128, h57, hlam]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              rcases p109_3 (m.d 0 3) (by simp) with h131 | h131
                              · linarith only [h131, hlam, p109_0]
                              · rcases p109_3 (m.d 1 3) (by simp) with h133 | h133
                                · linarith only [h133, h61, hlam]
                                · rcases p109_3 (m.d 2 3) (by simp) with h135 | h135
                                  · linarith only [h135, h64, hlam]
                                  · linarith only [h135, h3, hlam]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              rcases p109_3 (m.d 0 3) (by simp) with h138 | h138
                              · linarith only [h138, h39, hlam]
                              · linarith only [h1, h138, hlam]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h0, h107, h108, h3, h60, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p109_1]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h0, h107, h3, h60, h64, hlam, p109_2]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h57, hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h63, hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h107, hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [h108, hlam, p109_0]
                            · have p109_0 := h109c.1
                              have p109_1 := h109c.2.1
                              have p109_2 := h109c.2.2.1
                              have p109_3 := h109c.2.2.2
                              linarith only [hlam, p109_0]
                          · linarith only [h108, h3, h64, hc02, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h107, h3, h60, hc25, hlam, hphi, u5elo3]
                    · linarith only [h58, h60, h63, hc25, hlam, hphi, u5elo3]
                · linarith only [h60, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h57, hc03, hlam, hphi, ht34, ht45, u5elo3]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h155 | h155
      · rcases m.htr 0 2 3 (by decide) (by decide) with h156 | h156
        · linarith only [h0, h1, h156, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h158 | h158
          · rcases m.htr 0 3 5 (by decide) (by decide) with h159 | h159
            · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
              · linarith only [h0, h1, h156, h160, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h162 | h162
                · linarith only [h0, h1, h162, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · linarith only [h162, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h1, h159, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h166 | h166
            · rcases m.htr 1 2 3 (by decide) (by decide) with h167 | h167
              · linarith only [h0, h1, h167, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h169 | h169
                · linarith only [h0, h1, h169, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · linarith only [h169, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h1, h166, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
      · linarith only [h0, h155, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h174 | h174
    · rcases m.htr 0 1 5 (by decide) (by decide) with h175 | h175
      · rcases m.htr 0 2 3 (by decide) (by decide) with h176 | h176
        · rcases m.htr 0 3 4 (by decide) (by decide) with h177 | h177
          · rcases m.htr 0 3 5 (by decide) (by decide) with h178 | h178
            · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
              · rcases m.htr 1 2 5 (by decide) (by decide) with h180 | h180
                · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
                  · linarith only [h0, h174, h181, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h174, h177, h181, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h0, h180, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h174, h176, h179, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h177, h178, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h187 | h187
            · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
              · rcases m.htr 1 2 5 (by decide) (by decide) with h189 | h189
                · rcases m.htr 1 3 4 (by decide) (by decide) with h190 | h190
                  · linarith only [h174, h177, h187, h190, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                    · linarith only [h0, h174, h192, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h177, h187, h192, hc13, hc34, hlam, hphi]
                · linarith only [h0, h189, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h176, h188, hlam]
            · linarith only [h187, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h0, h174, h176, hlam]
      · linarith only [h174, h175, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h200 | h200
      · rcases m.htr 0 2 3 (by decide) (by decide) with h201 | h201
        · rcases m.htr 0 3 4 (by decide) (by decide) with h202 | h202
          · rcases m.htr 0 3 5 (by decide) (by decide) with h203 | h203
            · rcases m.htr 1 2 3 (by decide) (by decide) with h204 | h204
              · rcases m.htr 1 2 5 (by decide) (by decide) with h205 | h205
                · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h207 | h207
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h208 | h208
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h209 | h209
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
                          · linarith only [h0, h201, h208, h210, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h210, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h209, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h214 | h214
                        · linarith only [h174, h202, h208, h214, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h214, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h203, h207, hc13, hlam, hphi, ht34, ht45, u5elo0]
                  · linarith only [h174, h200, h202, h205, h206, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h205, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h200, h201, h204, hc02, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h202, h203, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h222 | h222
            · rcases m.htr 1 2 3 (by decide) (by decide) with h223 | h223
              · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
                · rcases m.htr 1 3 4 (by decide) (by decide) with h225 | h225
                  · linarith only [h174, h200, h202, h224, h225, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                      · linarith only [h174, h200, h201, h224, h225, h228, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h230 | h230
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h231 | h231
                          · rcases h3bigk with h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h174, hlam, p232_1]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h174, h225, hc23, hc34, hlam, hphi, p232_1]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h202, hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              rcases p232_3 (m.d 0 3) (by simp) with h237 | h237
                              · rcases p232_3 (m.d 1 3) (by simp) with h238 | h238
                                · rcases p232_3 (m.d 2 3) (by simp) with h239 | h239
                                  · linarith only [h201, h239, hlam]
                                  · linarith only [h230, h239, hlam]
                                · linarith only [h227, h238, hlam]
                              · linarith only [h237, hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h225, hc03, hc34, hlam, hphi, p232_1]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h225, h230, h231, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h225, hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              rcases p232_3 (m.d 0 3) (by simp) with h248 | h248
                              · linarith only [h174, h248, hlam]
                              · linarith only [h222, h248, hlam]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h201, hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h223, hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h228, hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h0, h201, h231, hc45, hlam, hphi, ht01, ht0b, ht5b, p232_1, u1elo1]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              rcases p232_3 (m.d 0 3) (by simp) with h256 | h256
                              · linarith only [h256, hlam, p232_0]
                              · rcases p232_3 (m.d 1 3) (by simp) with h258 | h258
                                · linarith only [h225, h258, hlam]
                                · linarith only [h174, h258, hlam]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h174, h200, h224, h230, h231, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p232_1]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              rcases p232_3 (m.d 0 3) (by simp) with h262 | h262
                              · linarith only [h202, h262, hlam]
                              · linarith only [h201, h262, hlam]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h174, h200, h224, h225, h230, hlam, p232_2]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h222, hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h227, hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h230, hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [h231, hlam, p232_0]
                            · have p232_0 := h232c.1
                              have p232_1 := h232c.2.1
                              have p232_2 := h232c.2.2.1
                              have p232_3 := h232c.2.2.2
                              linarith only [hlam, p232_0]
                          · linarith only [h174, h225, h231, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h230, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h174, h200, h222, h224, h227, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h224, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h201, h223, hlam]
            · linarith only [h222, hc03, hlam, hphi, ht34, ht45, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h278 | h278
          · rcases m.htr 0 3 5 (by decide) (by decide) with h279 | h279
            · rcases m.htr 1 2 3 (by decide) (by decide) with h280 | h280
              · linarith only [h0, h201, h280, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h282 | h282
                · rcases m.htr 1 3 4 (by decide) (by decide) with h283 | h283
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h284 | h284
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h285 | h285
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h286 | h286
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h287 | h287
                          · rcases h3bigk with h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [hlam, p288_0]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h174, hlam, p288_1]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h201, hlam, p288_1]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h174, h287, hc45, hlam, hphi, ht01, ht0b, ht5b, p288_1, u1elo2]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              rcases p288_3 (m.d 0 3) (by simp) with h293 | h293
                              · rcases p288_3 (m.d 1 3) (by simp) with h294 | h294
                                · rcases p288_3 (m.d 2 3) (by simp) with h295 | h295
                                  · rcases p288_3 (m.d 3 4) (by simp) with h296 | h296
                                    · linarith only [h278, h296, hlam]
                                    · linarith only [h287, h296, hlam]
                                  · linarith only [h286, h295, hlam]
                                · linarith only [h284, h294, hlam]
                              · linarith only [h293, hlam, p288_0]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h174, h200, h282, h286, h287, hc45, hlam, hphi, ht01, ht0b, ht5b, p288_1, u1elo2]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [hlam, p288_0]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h280, hlam, p288_1]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h287, hc45, hlam, hphi, ht01, ht0b, ht5b, p288_1, u1elo2]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              rcases p288_3 (m.d 0 3) (by simp) with h306 | h306
                              · linarith only [h174, h306, hlam]
                              · linarith only [h279, h306, hlam]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h278, h287, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p288_1]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h174, h200, h282, h286, h287, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p288_1]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [hlam, p288_0]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              rcases p288_3 (m.d 0 3) (by simp) with h312 | h312
                              · linarith only [h201, h312, hlam]
                              · linarith only [h278, h312, hlam]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h0, h200, h280, h282, h286, hlam, p288_2]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h278, hlam, p288_0]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h283, hlam, p288_0]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h285, hlam, p288_0]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [hlam, p288_0]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h174, h278, h287, hc45, hlam, hphi, ht01, ht0b, ht5b, p288_1, u1elo2]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h279, hlam, p288_0]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h284, hlam, p288_0]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h286, hlam, p288_0]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [h287, hlam, p288_0]
                            · have p288_0 := h288c.1
                              have p288_1 := h288c.2.1
                              have p288_2 := h288c.2.2.1
                              have p288_3 := h288c.2.2.2
                              linarith only [hlam, p288_0]
                          · linarith only [h287, hc34, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h280, h286, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h280, h285, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h174, h284, hc03, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h200, h278, h280, h282, h283, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h282, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h279, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h333 | h333
            · rcases m.htr 1 2 3 (by decide) (by decide) with h334 | h334
              · linarith only [h0, h200, h201, h334, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h336 | h336
                · rcases m.htr 1 3 4 (by decide) (by decide) with h337 | h337
                  · linarith only [h0, h200, h201, h278, h336, h337, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h339 | h339
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h340 | h340
                      · linarith only [h0, h200, h334, h336, h337, h340, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h200, h334, h336, h340, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h200, h334, h336, h339, hc25, hlam, hphi, u5elo3]
                · linarith only [h0, h336, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h200, h201, h333, hc15, hlam, hphi, u5elo3]
      · linarith only [h200, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem r1l7_11_13_25_L_I_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h4, h6, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h8, h9, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h12, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h14, h5, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                      · linarith only [h16, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                        · linarith only [h12, h16, h18, h5, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h16, h18, h5, h6, hc35, hlam, hphi, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
              · linarith only [h21, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                · linarith only [h23, h4, h5, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h25, h4, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h27 | h27
                    · linarith only [h2, h27, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h27, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
            · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
              · linarith only [h31, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                  · linarith only [h1, h34, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h33, h34, hc35, hlam, hphi, u3ehi3]
                · linarith only [h30, h33, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
              · linarith only [h30, h38, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                · rcases m.htr 1 3 5 (by decide) (by decide) with h41 | h41
                  · linarith only [h1, h41, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h40, h41, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
                  · linarith only [h40, h44, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                    · linarith only [h2, h46, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h51 | h51
                            · linarith only [h40, h46, h48, h51, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h40, h50, h51, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                          · linarith only [h40, h48, h50, hc45, hlam, hphi, ht34, u3ehi1]
                        · linarith only [h40, h48, h49, hc35, hlam, hphi, u3ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                        · linarith only [h48, h56, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h58 | h58
                          · linarith only [h40, h46, h48, h58, hc34, hlam, hphi, u3ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h60 | h60
                            · linarith only [h30, h40, h58, h60, hc34, hlam, hphi, u3ehi1]
                            · linarith only [h40, h60, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
          · linarith only [h0, h3, h63, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h65 | h65
            · rcases m.htr 1 2 5 (by decide) (by decide) with h66 | h66
              · linarith only [h1, h3, h63, h66, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h68 | h68
                · linarith only [h1, h3, h66, h68, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h63, h65, h68, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
              · linarith only [h63, h71, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                · linarith only [h1, h3, h73, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h75 | h75
                  · linarith only [h2, h3, h71, h73, h75, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h2, h3, h73, h75, hc35, hlam, hphi, u3ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h78 | h78
        · linarith only [h2, h78, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
          · linarith only [h0, h2, h80, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
            · linarith only [h1, h2, h80, h82, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h84 | h84
              · linarith only [h1, h2, h80, h82, h84, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                · linarith only [h1, h2, h82, h86, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h1, h2, h86, hc34, hlam, hphi, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
      · rcases m.htr 0 1 5 (by decide) (by decide) with h90 | h90
        · linarith only [h1, h90, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
          · linarith only [h0, h1, h92, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
            · rcases m.htr 1 2 5 (by decide) (by decide) with h95 | h95
              · linarith only [h0, h1, h92, h95, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h97 | h97
                · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h99 | h99
                    · linarith only [h0, h90, h92, h94, h98, h99, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h90, h94, h99, hc24, hc45, hlam, hphi]
                  · linarith only [h0, h1, h94, h97, h98, hc35, hlam, hphi, u3ehi3]
                · linarith only [h0, h1, h94, h97, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
              · linarith only [h104, h89, h94, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
                    · linarith only [h107, h108, h89, h90, h92, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h106, h108, h89, h90, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h1, h106, h107, h89, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h106, h89, h94, hc12, hc34, hlam, hphi, ht23]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h113 | h113
        · linarith only [h1, h113, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
          · linarith only [h0, h1, h115, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h117 | h117
            · linarith only [h0, h117, h89, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h119 | h119
              · linarith only [h0, h1, h115, h119, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h121 | h121
                · rcases m.htr 1 3 5 (by decide) (by decide) with h122 | h122
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                            · linarith only [h115, h121, h127, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases h1bigk with h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h113, h115, h121, h123, hc12, hc23, hlam, hphi, p129_1]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h1, hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h89, hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h113, hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h0, hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h115, hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h117, hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h119, hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h0, h115, hc12, hc23, hlam, hphi, p129_1]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                rcases p129_3 (m.d 0 1) (by simp) with h141 | h141
                                · linarith only [h1, h141, hlam]
                                · linarith only [h0, h141, hlam]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h115, h123, h127, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p129_1, u3ehi3]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h115, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p129_1, u5ehi1]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h0, h117, hc12, hc24, hlam, hphi, p129_1]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                rcases p129_3 (m.d 0 1) (by simp) with h148 | h148
                                · linarith only [h148, h89, hlam]
                                · linarith only [h0, h148, hlam]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h121, hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h0, h113, h115, h121, hc12, hc23, hlam, hphi, p129_1]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h0, h119, hc12, hc25, hlam, hphi, p129_1]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                rcases p129_3 (m.d 0 1) (by simp) with h155 | h155
                                · linarith only [h113, h155, hlam]
                                · linarith only [h0, h155, hlam]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h122, hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [h123, hlam, p129_0]
                              · have p129_0 := h129c.1
                                have p129_1 := h129c.2.1
                                have p129_2 := h129c.2.2.1
                                have p129_3 := h129c.2.2.2
                                linarith only [hlam, p129_0]
                          · linarith only [h0, h117, h126, h89, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h1, h115, h125, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h115, h122, h124, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · linarith only [h0, h123, h89, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h121, h122, hc35, hlam, hphi, u3ehi3]
                · linarith only [h0, h1, h121, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h167 | h167
    · rcases m.htr 0 1 4 (by decide) (by decide) with h168 | h168
      · rcases m.htr 0 1 5 (by decide) (by decide) with h169 | h169
        · linarith only [h0, h169, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
          · rcases m.htr 1 2 4 (by decide) (by decide) with h172 | h172
            · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
              · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                · linarith only [h167, h169, h173, h174, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h176 | h176
                  · linarith only [h168, h169, h173, h174, h176, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h168, h169, h174, h176, hc35, hlam, hphi, u3ehi1]
              · linarith only [h0, h167, h171, h173, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h167, h171, h172, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · linarith only [h0, h167, h171, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h182 | h182
        · linarith only [h0, h182, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h184 | h184
          · rcases m.htr 1 2 4 (by decide) (by decide) with h185 | h185
            · rcases m.htr 1 2 5 (by decide) (by decide) with h186 | h186
              · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
                · linarith only [h167, h168, h185, h187, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h167, h168, h187, hc34, hlam, hphi, u3ehi1]
              · linarith only [h167, h168, h184, h185, h186, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h167, h184, h185, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · linarith only [h0, h167, h184, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h193 | h193
      · rcases m.htr 0 1 5 (by decide) (by decide) with h194 | h194
        · linarith only [h0, h194, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h196 | h196
          · rcases m.htr 1 2 4 (by decide) (by decide) with h197 | h197
            · rcases m.htr 1 2 5 (by decide) (by decide) with h198 | h198
              · rcases m.htr 1 3 4 (by decide) (by decide) with h199 | h199
                · rcases m.htr 1 3 5 (by decide) (by decide) with h200 | h200
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h201 | h201
                    · linarith only [h193, h194, h196, h200, h201, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · linarith only [h193, h194, h199, h201, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h167, h193, h199, h200, hc35, hlam, hphi, u3ehi3]
                · linarith only [h167, h193, h199, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                · linarith only [h167, h193, h196, h198, h206, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h167, h193, h206, hlam]
            · linarith only [h167, h193, h196, h197, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h210 | h210
            · rcases m.htr 1 2 5 (by decide) (by decide) with h211 | h211
              · linarith only [h196, h211, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h213 | h213
                · linarith only [h0, h193, h196, h213, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h193, h196, h213, hlam]
            · linarith only [h0, h193, h210, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h217 | h217
        · linarith only [h0, h217, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h219 | h219
          · rcases m.htr 1 2 4 (by decide) (by decide) with h220 | h220
            · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
              · rcases m.htr 1 3 4 (by decide) (by decide) with h222 | h222
                · rcases m.htr 1 3 5 (by decide) (by decide) with h223 | h223
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h224 | h224
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h226 | h226
                        · linarith only [h219, h226, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h225, h226, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h229 | h229
                        · linarith only [h225, h229, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h231 | h231
                          · linarith only [h220, h231, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h233 | h233
                            · linarith only [h219, h222, h225, h231, h233, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h219, h222, h224, h225, h233, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h237 | h237
                        · linarith only [h219, h237, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h223, h236, h237, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h222, h224, h236, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h222, h223, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                  · linarith only [h222, h242, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
                      · linarith only [h167, h222, h245, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h247 | h247
                        · linarith only [h219, h242, h247, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h249 | h249
                          · linarith only [h220, h249, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h222, h244, h245, h249, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h252 | h252
                      · linarith only [h219, h242, h252, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h254 | h254
                        · linarith only [h219, h254, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h256 | h256
                          · linarith only [h220, h244, h256, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h258 | h258
                            · linarith only [h222, h244, h258, hc34, hlam, hphi, u3ehi1]
                            · linarith only [h167, h222, h258, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h261 | h261
                · rcases m.htr 1 3 5 (by decide) (by decide) with h262 | h262
                  · linarith only [h219, h221, h262, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h261, h262, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h265 | h265
                  · linarith only [h219, h221, h265, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h267 | h267
                    · linarith only [h220, h221, h267, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                      · linarith only [h219, h221, h269, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h271 | h271
                        · linarith only [h220, h221, h265, h269, h271, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h220, h221, h269, h271, hc35, hlam, hphi, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h274 | h274
              · linarith only [h220, h274, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h276 | h276
                · linarith only [h219, h220, h276, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h278 | h278
                  · linarith only [h276, h278, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h280 | h280
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                      · linarith only [h167, h276, h281, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h219, h220, h281, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h219, h220, h280, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h285 | h285
            · rcases m.htr 1 2 5 (by decide) (by decide) with h286 | h286
              · linarith only [h219, h286, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
                · rcases m.htr 1 3 5 (by decide) (by decide) with h289 | h289
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h290 | h290
                    · linarith only [h219, h285, h290, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h292 | h292
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h293 | h293
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h294 | h294
                          · linarith only [h285, h286, h290, h293, h294, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h285, h286, h292, h294, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h219, h285, h289, h292, h293, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h219, h289, h292, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · linarith only [h288, h289, hc35, hlam, hphi, u3ehi3]
                · linarith only [h219, h285, h288, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h301 | h301
              · linarith only [h219, h301, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h303 | h303
                · rcases m.htr 1 3 5 (by decide) (by decide) with h304 | h304
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h306 | h306
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h307 | h307
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h308 | h308
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h309 | h309
                            · linarith only [h303, h309, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases h1bigk with h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c
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
                                linarith only [h167, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h193, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h217, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h301, h306, h308, hc01, hc23, hlam, hphi, ht12, p311_1]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h219, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h285, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h301, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                rcases p311_3 (m.d 0 1) (by simp) with h322 | h322
                                · linarith only [h322, hlam, p311_0]
                                · rcases p311_3 (m.d 1 2) (by simp) with h324 | h324
                                  · linarith only [h219, h324, hlam]
                                  · linarith only [h0, h324, hlam]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h0, h219, hc01, hc23, hlam, hphi, ht12, p311_1]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h219, h305, h309, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p311_1, u3ehi3]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h219, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p311_1, u5ehi1]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                rcases p311_3 (m.d 0 1) (by simp) with h331 | h331
                                · linarith only [h331, hlam, p311_0]
                                · rcases p311_3 (m.d 1 2) (by simp) with h333 | h333
                                  · linarith only [h285, h333, hlam]
                                  · linarith only [h0, h333, hlam]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p311_1]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h303, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h285, h305, h306, h309, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p311_1, u3ehi3]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                rcases p311_3 (m.d 0 1) (by simp) with h340 | h340
                                · linarith only [h340, hlam, p311_0]
                                · rcases p311_3 (m.d 1 2) (by simp) with h342 | h342
                                  · linarith only [h301, h342, hlam]
                                  · linarith only [h0, h342, hlam]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p311_1]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h304, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [h305, hlam, p311_0]
                              · have p311_0 := h311c.1
                                have p311_1 := h311c.2.1
                                have p311_2 := h311c.2.2.1
                                have p311_3 := h311c.2.2.2
                                linarith only [hlam, p311_0]
                          · linarith only [h0, h285, h308, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h219, h303, h305, h307, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h219, h303, h305, h306, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h352 | h352
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h353 | h353
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h354 | h354
                          · linarith only [h193, h305, h354, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h285, h354, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h219, h304, h353, hlam]
                      · linarith only [h219, h304, h352, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · linarith only [h303, h304, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h360 | h360
                  · linarith only [h303, h360, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h362 | h362
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                      · linarith only [h167, h303, h363, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h219, h363, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h366 | h366
                      · linarith only [h0, h219, h303, h366, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h219, h366, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
