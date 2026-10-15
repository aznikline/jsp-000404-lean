import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_M_LI_L_I_L_0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h12, h15, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h0, h12, h14, h15, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                              · linarith only [h14, h18, h2, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · rcases h2bigk with h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [hc12, hlam, hphi, p20_1, u2elo0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h13, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p20_1, u2elo0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  rcases p20_3 (m.d 0 2) (by simp) with h24 | h24
                                  · rcases p20_3 (m.d 1 2) (by simp) with h25 | h25
                                    · linarith only [h0, h25, hlam]
                                    · linarith only [h25, h8, hlam]
                                  · linarith only [h24, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  rcases p20_3 (m.d 0 2) (by simp) with h29 | h29
                                  · rcases p20_3 (m.d 1 2) (by simp) with h30 | h30
                                    · linarith only [h0, h30, hlam]
                                    · linarith only [h30, h9, hlam]
                                  · linarith only [h29, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h0, hlam, p20_1]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h13, h18, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo1]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  rcases p20_3 (m.d 0 2) (by simp) with h37 | h37
                                  · rcases p20_3 (m.d 1 2) (by simp) with h38 | h38
                                    · rcases p20_3 (m.d 2 3) (by simp) with h39 | h39
                                      · linarith only [h39, h7, hlam]
                                      · linarith only [h12, h39, hlam]
                                    · linarith only [h38, hlam, p20_0]
                                  · linarith only [h3, h37, hlam]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  rcases p20_3 (m.d 0 2) (by simp) with h44 | h44
                                  · rcases p20_3 (m.d 1 2) (by simp) with h45 | h45
                                    · rcases p20_3 (m.d 2 3) (by simp) with h46 | h46
                                      · linarith only [h46, h7, hlam]
                                      · linarith only [h13, h46, hlam]
                                    · linarith only [h45, hlam, p20_0]
                                  · linarith only [h4, h44, hlam]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h2, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h7, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h12, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h0, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p20_1, u2elo0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h3, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h8, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h12, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h14, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h4, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h9, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h13, hlam, p20_0]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [h12, hc34, hlam, hphi, ht45, p20_1, u5elo2]
                                · have p20_0 := h20c.1
                                  have p20_1 := h20c.2.1
                                  have p20_2 := h20c.2.2.1
                                  have p20_3 := h20c.2.2.2
                                  linarith only [hlam, p20_0]
                          · linarith only [h1, h11, h12, h13, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                          · linarith only [h12, h2, h5, h67, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h70 | h70
                              · rcases h2bigk with h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hc12, hlam, hphi, p71_1, u2elo0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  rcases p71_3 (m.d 0 2) (by simp) with h74 | h74
                                  · rcases p71_3 (m.d 1 2) (by simp) with h75 | h75
                                    · linarith only [h0, h75, hlam]
                                    · linarith only [h7, h75, hlam]
                                  · linarith only [h74, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h69, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p71_1, u2elo0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  rcases p71_3 (m.d 0 2) (by simp) with h80 | h80
                                  · rcases p71_3 (m.d 1 2) (by simp) with h81 | h81
                                    · linarith only [h0, h81, hlam]
                                    · linarith only [h81, h9, hlam]
                                  · linarith only [h80, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h0, hlam, p71_1]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  rcases p71_3 (m.d 0 2) (by simp) with h87 | h87
                                  · rcases p71_3 (m.d 1 2) (by simp) with h88 | h88
                                    · rcases p71_3 (m.d 2 3) (by simp) with h89 | h89
                                      · linarith only [h89, hlam, p71_0]
                                      · rcases p71_3 (m.d 2 4) (by simp) with h91 | h91
                                        · linarith only [h8, h91, hlam]
                                        · linarith only [h12, h91, hlam]
                                    · linarith only [h88, hlam, p71_0]
                                  · linarith only [h2, h87, hlam]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h69, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p71_1, u2elo1]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  rcases p71_3 (m.d 0 2) (by simp) with h97 | h97
                                  · rcases p71_3 (m.d 1 2) (by simp) with h98 | h98
                                    · rcases p71_3 (m.d 2 3) (by simp) with h99 | h99
                                      · linarith only [h7, h99, hlam]
                                      · rcases p71_3 (m.d 2 4) (by simp) with h101 | h101
                                        · linarith only [h101, h8, hlam]
                                        · linarith only [h101, h69, hlam]
                                    · linarith only [h98, hlam, p71_0]
                                  · linarith only [h4, h97, hlam]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h2, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h7, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h12, hlam, p71_1]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h67, hlam, p71_1]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h3, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h8, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p71_1, u2elo0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h1, h10, h12, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p71_1, u2elo0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h4, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h9, hlam, p71_0]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p71_1, u5elo2]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [h69, hlam, p71_1]
                                · have p71_0 := h71c.1
                                  have p71_1 := h71c.2.1
                                  have p71_2 := h71c.2.2.1
                                  have p71_3 := h71c.2.2.2
                                  linarith only [hlam, p71_0]
                              · linarith only [h12, h70, hc23, hlam, hphi, ht34, ht45, u5elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                              · linarith only [h122, h2, h5, h69, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · linarith only [h12, h122, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h10, h11, h2, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h126 | h126
                      · linarith only [h10, h126, h2, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                        · linarith only [h10, h128, h2, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h130 | h130
                          · linarith only [h126, h130, h7, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h132 | h132
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h133 | h133
                              · rcases h2bigk with h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [hlam, p134_0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [hc12, hlam, hphi, p134_1, u2elo0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  rcases p134_3 (m.d 0 2) (by simp) with h137 | h137
                                  · rcases p134_3 (m.d 1 2) (by simp) with h138 | h138
                                    · linarith only [h0, h138, hlam]
                                    · linarith only [h138, h7, hlam]
                                  · linarith only [h137, hlam, p134_0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h132, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p134_1, u2elo0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  rcases p134_3 (m.d 0 2) (by simp) with h143 | h143
                                  · rcases p134_3 (m.d 1 2) (by simp) with h144 | h144
                                    · linarith only [h0, h144, hlam]
                                    · linarith only [h144, h9, hlam]
                                  · linarith only [h143, hlam, p134_0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h0, hlam, p134_1]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [hlam, p134_0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  rcases p134_3 (m.d 0 2) (by simp) with h150 | h150
                                  · rcases p134_3 (m.d 1 2) (by simp) with h151 | h151
                                    · rcases p134_3 (m.d 2 3) (by simp) with h152 | h152
                                      · linarith only [h152, hlam, p134_0]
                                      · rcases p134_3 (m.d 2 4) (by simp) with h154 | h154
                                        · linarith only [h154, h8, hlam]
                                        · linarith only [h128, h154, hlam]
                                    · linarith only [h151, hlam, p134_0]
                                  · linarith only [h150, h2, hlam]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h132, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p134_1, u2elo1]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  rcases p134_3 (m.d 0 2) (by simp) with h160 | h160
                                  · rcases p134_3 (m.d 1 2) (by simp) with h161 | h161
                                    · rcases p134_3 (m.d 2 3) (by simp) with h162 | h162
                                      · linarith only [h162, h7, hlam]
                                      · rcases p134_3 (m.d 2 4) (by simp) with h164 | h164
                                        · linarith only [h164, h8, hlam]
                                        · linarith only [h132, h164, hlam]
                                    · linarith only [h161, hlam, p134_0]
                                  · linarith only [h160, h4, hlam]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h2, hlam, p134_0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h7, hlam, p134_0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [hlam, p134_0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h128, hlam, p134_1]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h130, hlam, p134_1]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h3, hlam, p134_0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h8, hlam, p134_0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p134_1, u2elo0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [hlam, p134_0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h10, h2, h5, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p134_1, u2elo0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h4, hlam, p134_0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h9, hlam, p134_0]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p134_1, u5elo2]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [h132, hlam, p134_1]
                                · have p134_0 := h134c.1
                                  have p134_1 := h134c.2.1
                                  have p134_2 := h134c.2.2.1
                                  have p134_3 := h134c.2.2.2
                                  linarith only [hlam, p134_0]
                              · linarith only [h10, h133, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h185 | h185
                              · linarith only [h132, h185, h2, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                              · linarith only [h10, h185, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h4, h9, hc12, hlam, hphi, u2elo0]
                · linarith only [h3, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h2, h7, hc12, hlam, hphi, u2elo0]
            · linarith only [h5, h6, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h192 | h192
            · rcases m.htr 1 2 3 (by decide) (by decide) with h193 | h193
              · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
                · rcases m.htr 1 2 5 (by decide) (by decide) with h195 | h195
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h196 | h196
                    · linarith only [h1, h192, h196, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h198 | h198
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h199 | h199
                        · linarith only [h0, h1, h193, h198, h199, h5, hc02, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h201 | h201
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h202 | h202
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h203 | h203
                              · rcases h2bigk with h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [hlam, p204_0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h194, h199, h201, h203, hc02, hc45, hlam, hphi, ht0b, ht5b, p204_1]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h201, h203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p204_1, u2elo0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h199, h201, h203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p204_1, u2elo0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  rcases p204_3 (m.d 0 2) (by simp) with h209 | h209
                                  · rcases p204_3 (m.d 1 2) (by simp) with h210 | h210
                                    · linarith only [h0, h210, hlam]
                                    · linarith only [h195, h210, hlam]
                                  · linarith only [h209, hlam, p204_0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h0, hlam, p204_1]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [hlam, p204_0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h201, h203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p204_1, u2elo1]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h0, h199, h201, h203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p204_1, u2elo0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  rcases p204_3 (m.d 0 2) (by simp) with h218 | h218
                                  · rcases p204_3 (m.d 1 2) (by simp) with h219 | h219
                                    · rcases p204_3 (m.d 2 3) (by simp) with h220 | h220
                                      · linarith only [h193, h220, hlam]
                                      · linarith only [h201, h220, hlam]
                                    · linarith only [h219, hlam, p204_0]
                                  · linarith only [h218, h4, hlam]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h2, hlam, p204_0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h193, hlam, p204_0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [hlam, p204_0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h199, hlam, p204_1]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p204_1, u2elo0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h3, hlam, p204_0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h194, hlam, p204_0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h201, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p204_1, u2elo3]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [hlam, p204_0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h0, h194, h201, h203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p204_1, u2elo0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h4, hlam, p204_0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h195, hlam, p204_0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h201, hlam, p204_0]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [h202, hlam, p204_1]
                                · have p204_0 := h204c.1
                                  have p204_1 := h204c.2.1
                                  have p204_2 := h204c.2.2.1
                                  have p204_3 := h204c.2.2.2
                                  linarith only [hlam, p204_0]
                              · linarith only [h203, h5, hc03, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h199, h201, h202, hc35, hlam, hphi, u5elo4]
                          · linarith only [h192, h201, h5, hc23, hc34, hlam, hphi]
                      · linarith only [h192, h198, h5, hc13, hc34, hlam, hphi]
                  · linarith only [h195, h4, hc12, hlam, hphi, u2elo0]
                · linarith only [h193, h194, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h193, h2, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h247 | h247
              · rcases m.htr 1 2 4 (by decide) (by decide) with h248 | h248
                · rcases m.htr 1 2 5 (by decide) (by decide) with h249 | h249
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h250 | h250
                    · linarith only [h1, h192, h250, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h252 | h252
                      · linarith only [h1, h192, h252, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h254 | h254
                        · linarith only [h2, h254, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h256 | h256
                          · linarith only [h1, h192, h247, h256, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h258 | h258
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h259 | h259
                              · rcases h2bigk with h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [hlam, p260_0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [hc12, hlam, hphi, p260_1, u2elo0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  rcases p260_3 (m.d 0 2) (by simp) with h263 | h263
                                  · rcases p260_3 (m.d 1 2) (by simp) with h264 | h264
                                    · linarith only [h0, h264, hlam]
                                    · linarith only [h247, h264, hlam]
                                  · linarith only [h263, hlam, p260_0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h258, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p260_1, u2elo0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  rcases p260_3 (m.d 0 2) (by simp) with h269 | h269
                                  · rcases p260_3 (m.d 1 2) (by simp) with h270 | h270
                                    · linarith only [h0, h270, hlam]
                                    · linarith only [h249, h270, hlam]
                                  · linarith only [h269, hlam, p260_0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h0, hlam, p260_1]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [hlam, p260_0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  rcases p260_3 (m.d 0 2) (by simp) with h276 | h276
                                  · rcases p260_3 (m.d 1 2) (by simp) with h277 | h277
                                    · rcases p260_3 (m.d 2 3) (by simp) with h278 | h278
                                      · linarith only [h278, hlam, p260_0]
                                      · rcases p260_3 (m.d 2 4) (by simp) with h280 | h280
                                        · linarith only [h248, h280, hlam]
                                        · linarith only [h254, h280, hlam]
                                    · linarith only [h277, hlam, p260_0]
                                  · linarith only [h2, h276, hlam]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h258, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p260_1, u2elo1]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  rcases p260_3 (m.d 0 2) (by simp) with h286 | h286
                                  · rcases p260_3 (m.d 1 2) (by simp) with h287 | h287
                                    · rcases p260_3 (m.d 2 3) (by simp) with h288 | h288
                                      · linarith only [h247, h288, hlam]
                                      · rcases p260_3 (m.d 2 4) (by simp) with h290 | h290
                                        · linarith only [h248, h290, hlam]
                                        · linarith only [h258, h290, hlam]
                                    · linarith only [h287, hlam, p260_0]
                                  · linarith only [h286, h4, hlam]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h2, hlam, p260_0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h247, hlam, p260_0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [hlam, p260_0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h254, hlam, p260_1]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h256, hlam, p260_1]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h3, hlam, p260_0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h248, hlam, p260_0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p260_1, u2elo0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [hlam, p260_0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h0, h248, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p260_1, u2elo0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h4, hlam, p260_0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h249, hlam, p260_0]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, ht45, p260_1, u5elo2]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [h258, hlam, p260_1]
                                · have p260_0 := h260c.1
                                  have p260_1 := h260c.2.1
                                  have p260_2 := h260c.2.2.1
                                  have p260_3 := h260c.2.2.2
                                  linarith only [hlam, p260_0]
                              · linarith only [h259, h5, hc03, hlam, hphi, ht34, ht45, u5elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h311 | h311
                              · rcases h2bigk with h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c | h312c
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [hc12, hlam, hphi, p312_1, u2elo0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  rcases p312_3 (m.d 0 2) (by simp) with h315 | h315
                                  · rcases p312_3 (m.d 1 2) (by simp) with h316 | h316
                                    · linarith only [h0, h316, hlam]
                                    · linarith only [h247, h316, hlam]
                                  · linarith only [h315, hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  rcases p312_3 (m.d 0 2) (by simp) with h320 | h320
                                  · rcases p312_3 (m.d 1 2) (by simp) with h321 | h321
                                    · linarith only [h0, h321, hlam]
                                    · linarith only [h248, h321, hlam]
                                  · linarith only [h320, hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  rcases p312_3 (m.d 0 2) (by simp) with h325 | h325
                                  · rcases p312_3 (m.d 1 2) (by simp) with h326 | h326
                                    · linarith only [h0, h326, hlam]
                                    · linarith only [h249, h326, hlam]
                                  · linarith only [h325, hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h0, hlam, p312_1]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  rcases p312_3 (m.d 0 2) (by simp) with h332 | h332
                                  · rcases p312_3 (m.d 1 2) (by simp) with h333 | h333
                                    · rcases p312_3 (m.d 2 3) (by simp) with h334 | h334
                                      · linarith only [h334, hlam, p312_0]
                                      · rcases p312_3 (m.d 2 4) (by simp) with h336 | h336
                                        · linarith only [h248, h336, hlam]
                                        · linarith only [h254, h336, hlam]
                                    · linarith only [h333, hlam, p312_0]
                                  · linarith only [h2, h332, hlam]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  rcases p312_3 (m.d 0 2) (by simp) with h341 | h341
                                  · rcases p312_3 (m.d 1 2) (by simp) with h342 | h342
                                    · rcases p312_3 (m.d 2 3) (by simp) with h343 | h343
                                      · linarith only [h247, h343, hlam]
                                      · rcases p312_3 (m.d 2 4) (by simp) with h345 | h345
                                        · linarith only [h345, hlam, p312_0]
                                        · rcases p312_3 (m.d 2 5) (by simp) with h347 | h347
                                          · linarith only [h249, h347, hlam]
                                          · linarith only [h258, h347, hlam]
                                    · linarith only [h342, hlam, p312_0]
                                  · linarith only [h3, h341, hlam]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  rcases p312_3 (m.d 0 2) (by simp) with h352 | h352
                                  · rcases p312_3 (m.d 1 2) (by simp) with h353 | h353
                                    · rcases p312_3 (m.d 2 3) (by simp) with h354 | h354
                                      · linarith only [h247, h354, hlam]
                                      · rcases p312_3 (m.d 2 4) (by simp) with h356 | h356
                                        · linarith only [h248, h356, hlam]
                                        · rcases p312_3 (m.d 2 5) (by simp) with h358 | h358
                                          · linarith only [h358, hlam, p312_0]
                                          · rcases h3bigk with h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [hlam, p360_0]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h247, h5, hc23, hc34, hlam, hphi, p360_1]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h5, hc23, hc34, hlam, hphi, p360_1]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h5, hlam, p360_0]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h192, hlam, p360_0]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h1, hlam, p360_0]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [hlam, p360_0]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h1, h5, hc23, hc34, hlam, hphi, p360_1]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h250, hlam, p360_0]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h252, hlam, p360_0]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h2, hlam, p360_1]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h247, hlam, p360_1]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [hlam, p360_0]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h254, hlam, p360_0]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h256, hlam, p360_0]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              rcases p360_3 (m.d 0 3) (by simp) with h376 | h376
                                              · linarith only [h376, hlam, p360_0]
                                              · rcases p360_3 (m.d 1 3) (by simp) with h378 | h378
                                                · linarith only [h250, h378, hlam]
                                                · rcases p360_3 (m.d 2 3) (by simp) with h380 | h380
                                                  · linarith only [h254, h380, hlam]
                                                  · rcases p360_3 (m.d 3 4) (by simp) with h382 | h382
                                                    · rcases p360_3 (m.d 3 5) (by simp) with h383 | h383
                                                      · linarith only [h311, h383, hlam]
                                                      · linarith only [h192, h383, hlam]
                                                    · linarith only [h382, hlam, p360_0]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              rcases p360_3 (m.d 0 3) (by simp) with h387 | h387
                                              · linarith only [h387, h5, hlam]
                                              · linarith only [h1, h387, hlam]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              rcases p360_3 (m.d 0 3) (by simp) with h390 | h390
                                              · linarith only [h390, h5, hlam]
                                              · linarith only [h2, h390, hlam]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [hlam, p360_0]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h192, hc03, hc34, hlam, hphi, p360_1]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h1, hc13, hlam, hphi, ht34, ht45, p360_1, u5elo3]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h247, hc23, hlam, hphi, ht34, ht45, p360_1, u5elo3]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [hc23, hlam, hphi, ht34, ht45, p360_1, u5elo3]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [h311, hlam, p360_1]
                                            · have p360_0 := h360c.1
                                              have p360_1 := h360c.2.1
                                              have p360_2 := h360c.2.2.1
                                              have p360_3 := h360c.2.2.2
                                              linarith only [hlam, p360_0]
                                    · linarith only [h353, hlam, p312_0]
                                  · linarith only [h352, h4, hlam]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h2, hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h247, hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h254, hlam, p312_1]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h256, hlam, p312_1]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h3, hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h248, hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h258, hc23, hlam, hphi, ht34, ht45, p312_1, u5elo2]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h258, hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h4, hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h249, hlam, p312_0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h0, h249, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p312_1, u2elo0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [h0, h249, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p312_1, u2elo0]
                                · have p312_0 := h312c.1
                                  have p312_1 := h312c.2.1
                                  have p312_2 := h312c.2.2.1
                                  have p312_3 := h312c.2.2.2
                                  linarith only [hlam, p312_0]
                              · linarith only [h1, h247, h311, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h249, h4, hc12, hlam, hphi, u2elo0]
                · linarith only [h247, h248, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h2, h247, hc12, hlam, hphi, u2elo0]
        · linarith only [h2, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h422 | h422
        · rcases m.htr 0 3 4 (by decide) (by decide) with h423 | h423
          · linarith only [h2, h3, h423, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h425 | h425
            · rcases m.htr 1 2 3 (by decide) (by decide) with h426 | h426
              · rcases m.htr 1 2 4 (by decide) (by decide) with h427 | h427
                · linarith only [h0, h3, h427, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h429 | h429
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h430 | h430
                    · linarith only [h1, h423, h425, h430, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h432 | h432
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h433 | h433
                        · linarith only [h0, h1, h3, h423, h426, h432, h433, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h435 | h435
                          · linarith only [h0, h3, h426, h435, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                          · linarith only [h1, h2, h3, h432, h435, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · linarith only [h2, h3, h425, h432, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h3, h422, h429, hc12, hlam, hphi, u2elo3]
              · linarith only [h2, h3, h426, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
              · rcases m.htr 1 2 4 (by decide) (by decide) with h442 | h442
                · linarith only [h3, h442, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h444 | h444
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h445 | h445
                    · linarith only [h1, h423, h445, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h447 | h447
                      · linarith only [h1, h425, h447, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h449 | h449
                        · linarith only [h0, h1, h3, h423, h441, h449, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h451 | h451
                          · linarith only [h2, h3, h451, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h453 | h453
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h454 | h454
                              · rcases h2bigk with h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c | h455c
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h3, h444, h451, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p455_1, u2elo3]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p455_1, u2elo3]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h3, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h3, h451, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p455_1, u2elo3]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h0, hlam, p455_1]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h0, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p455_1, u2elo3]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h442, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h0, h3, h451, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p455_1, u2elo3]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h2, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h441, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h449, hlam, p455_1]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h451, hlam, p455_1]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hc02, hlam, hphi, p455_1, u2elo3]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h441, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p455_1, u2elo3]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  rcases p455_3 (m.d 0 2) (by simp) with h473 | h473
                                  · linarith only [h3, h473, hlam]
                                  · linarith only [h2, h473, hlam]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  rcases p455_3 (m.d 0 2) (by simp) with h477 | h477
                                  · linarith only [h3, h477, hlam]
                                  · linarith only [h422, h477, hlam]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h422, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h444, hlam, p455_0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h0, h444, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p455_1, u2elo0]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [h453, hlam, p455_1]
                                · have p455_0 := h455c.1
                                  have p455_1 := h455c.2.1
                                  have p455_2 := h455c.2.2.1
                                  have p455_3 := h455c.2.2.2
                                  linarith only [hlam, p455_0]
                              · linarith only [h0, h3, h444, h449, h453, h454, hlam]
                            · linarith only [h3, h453, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h441, h444, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · linarith only [h2, h3, h441, hc12, hlam, hphi, u2elo3]
        · linarith only [h2, h422, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h490 | h490
      · rcases m.htr 0 2 5 (by decide) (by decide) with h491 | h491
        · rcases m.htr 0 3 4 (by decide) (by decide) with h492 | h492
          · rcases m.htr 0 3 5 (by decide) (by decide) with h493 | h493
            · rcases m.htr 1 2 3 (by decide) (by decide) with h494 | h494
              · linarith only [h2, h490, h494, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h496 | h496
                · rcases m.htr 1 2 5 (by decide) (by decide) with h497 | h497
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h498 | h498
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h499 | h499
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h500 | h500
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h501 | h501
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h502 | h502
                            · linarith only [h0, h2, h496, h502, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h504 | h504
                              · linarith only [h500, h502, h504, hlam]
                              · rcases h2bigk with h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h2, hc12, hlam, hphi, p506_1, u2elo2]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h2, hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h2, h500, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p506_1, u2elo2]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h2, h500, h502, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p506_1, u2elo2]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h0, hlam, p506_1]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h494, hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h0, h2, h500, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p506_1, u2elo2]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h0, h2, h500, h502, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p506_1, u2elo2]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [hc02, hlam, hphi, p506_1, u2elo2]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [hc12, hlam, hphi, p506_1, u2elo2]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  rcases p506_3 (m.d 0 2) (by simp) with h520 | h520
                                  · linarith only [h2, h520, hlam]
                                  · linarith only [h490, h520, hlam]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  rcases p506_3 (m.d 0 2) (by simp) with h523 | h523
                                  · linarith only [h2, h523, hlam]
                                  · linarith only [h491, h523, hlam]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h490, hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h496, hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h500, hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h502, hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h491, hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h497, hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h501, hlam, p506_0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [h0, h497, h500, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p506_1, u2elo0]
                                · have p506_0 := h506c.1
                                  have p506_1 := h506c.2.1
                                  have p506_2 := h506c.2.2.1
                                  have p506_3 := h506c.2.2.2
                                  linarith only [hlam, p506_0]
                          · linarith only [h2, h501, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h2, h492, h496, h500, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h493, h494, h496, h499, hc24, hlam, hphi, ht45, u5elo0]
                    · linarith only [h2, h490, h492, h494, h496, h498, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h496, h497, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h2, h490, h496, hc12, hlam, hphi, u2elo2]
            · linarith only [h2, h490, h493, hc24, hlam, hphi, ht45, u5elo3]
          · linarith only [h2, h490, h492, hlam]
        · linarith only [h490, h491, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h545 | h545
        · rcases m.htr 0 3 4 (by decide) (by decide) with h546 | h546
          · rcases m.htr 0 3 5 (by decide) (by decide) with h547 | h547
            · rcases m.htr 1 2 3 (by decide) (by decide) with h548 | h548
              · linarith only [h2, h548, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h550 | h550
                · linarith only [h0, h490, h550, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h552 | h552
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h553 | h553
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h554 | h554
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h555 | h555
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h556 | h556
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h557 | h557
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h558 | h558
                              · rcases h2bigk with h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c | h559c
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [hlam, p559_0]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h490, h552, h555, h556, h558, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p559_1, u2elo2]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h2, hlam, p559_0]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h490, hlam, p559_0]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h490, h555, h556, h558, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p559_1, u2elo2]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h0, hlam, p559_1]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [hlam, p559_0]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h548, hlam, p559_0]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h550, hlam, p559_0]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h0, h490, h555, h556, h558, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p559_1, u2elo2]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [hc02, hlam, hphi, p559_1, u2elo2]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [hc12, hlam, hphi, p559_1, u2elo2]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [hlam, p559_0]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h490, h545, h556, h558, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p559_1, u2elo2]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  rcases p559_3 (m.d 0 2) (by simp) with h574 | h574
                                  · linarith only [h2, h574, hlam]
                                  · linarith only [h545, h574, hlam]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h0, h552, h556, h558, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p559_1, u2elo3]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h552, h556, h558, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p559_1, u2elo3]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h555, hlam, p559_0]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [hlam, p559_0]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  rcases p559_3 (m.d 0 2) (by simp) with h581 | h581
                                  · linarith only [h490, h581, hlam]
                                  · linarith only [h545, h581, hlam]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h545, hlam, p559_0]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h552, hlam, p559_0]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h556, hlam, p559_0]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [h557, hlam, p559_1]
                                · have p559_0 := h559c.1
                                  have p559_1 := h559c.2.1
                                  have p559_2 := h559c.2.2.1
                                  have p559_3 := h559c.2.2.2
                                  linarith only [hlam, p559_0]
                              · linarith only [h0, h2, h552, h557, h558, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                            · linarith only [h0, h490, h552, h556, h557, hc35, hlam, hphi, u5elo4]
                          · linarith only [h2, h556, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h0, h1, h2, h552, h553, h555, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h490, h545, h547, h548, h552, h554, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h2, h546, h548, h552, h553, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h490, h545, h552, hc12, hlam, hphi, u2elo3]
            · linarith only [h546, h547, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h597 | h597
            · rcases m.htr 1 2 3 (by decide) (by decide) with h598 | h598
              · linarith only [h0, h2, h598, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h600 | h600
                · linarith only [h0, h490, h600, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h602 | h602
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h603 | h603
                    · linarith only [h0, h1, h2, h546, h602, h603, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h605 | h605
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h606 | h606
                        · linarith only [h0, h2, h546, h602, h606, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h608 | h608
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h609 | h609
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h610 | h610
                              · rcases h2bigk with h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h602, h608, h610, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p611_1, u2elo0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h2, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h490, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h2, h606, h608, h610, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h0, hlam, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h598, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h600, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h0, h2, h606, h608, h610, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h606, hc02, hc34, hlam, hphi, ht23, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h606, hc12, hc34, hlam, hphi, ht23, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h606, hlam, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  rcases p611_3 (m.d 0 2) (by simp) with h626 | h626
                                  · linarith only [h2, h626, hlam]
                                  · linarith only [h545, h626, hlam]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h0, h602, h608, h610, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p611_1, u2elo3]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h602, h608, h610, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p611_1, u2elo3]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h0, h2, h602, h608, h610, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p611_1, u2elo3]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  rcases p611_3 (m.d 0 2) (by simp) with h633 | h633
                                  · linarith only [h490, h633, hlam]
                                  · linarith only [h545, h633, hlam]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h545, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h602, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h608, hlam, p611_0]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [h609, hlam, p611_1]
                                · have p611_0 := h611c.1
                                  have p611_1 := h611c.2.1
                                  have p611_2 := h611c.2.2.1
                                  have p611_3 := h611c.2.2.2
                                  linarith only [hlam, p611_0]
                              · linarith only [h2, h546, h610, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h0, h490, h602, h608, h609, hc35, hlam, hphi, u5elo4]
                          · linarith only [h0, h2, h602, h608, hc25, hlam, hphi, u5elo3]
                      · linarith only [h546, h597, h605, hc13, hc34, hlam, hphi]
                  · linarith only [h545, h602, hc12, hlam, hphi, u2elo0]
            · linarith only [h2, h545, h597, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h647 | h647
          · rcases m.htr 0 3 5 (by decide) (by decide) with h648 | h648
            · rcases m.htr 1 2 3 (by decide) (by decide) with h649 | h649
              · linarith only [h0, h545, h649, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h651 | h651
                · linarith only [h0, h545, h651, hc24, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h653 | h653
                  · linarith only [h0, h545, h653, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h655 | h655
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h656 | h656
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h657 | h657
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h658 | h658
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h659 | h659
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h660 | h660
                              · rcases h2bigk with h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h545, hc12, hlam, hphi, ht23, ht34, ht45, p661_1, u5elo2]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h2, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h490, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h545, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h0, hlam, p661_1]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h649, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h651, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h653, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hc02, hlam, hphi, p661_1, u2elo2]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hc12, hlam, hphi, p661_1, u2elo2]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h0, h490, hc12, hlam, hphi, p661_1, u2elo2]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h0, h545, hc12, hlam, hphi, p661_1, u2elo2]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p661_1, u2elo3]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hc12, hlam, hphi, p661_1, u2elo3]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h657, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h0, h545, h657, hc12, hlam, hphi, p661_1, u2elo2]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p661_1, u2elo4]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p661_1, u5elo2]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h658, hlam, p661_0]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [h659, hlam, p661_1]
                                · have p661_0 := h661c.1
                                  have p661_1 := h661c.2.1
                                  have p661_2 := h661c.2.2.1
                                  have p661_3 := h661c.2.2.2
                                  linarith only [hlam, p661_0]
                              · rcases h2bigk with h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c | h687c
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [hlam, p687_0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [hc12, hlam, hphi, p687_1, u2elo0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h2, hlam, p687_0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h490, hlam, p687_0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h545, hlam, p687_0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h0, hlam, p687_1]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [hlam, p687_0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h649, hlam, p687_0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h651, hlam, p687_0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h653, hlam, p687_0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [hc02, hlam, hphi, p687_1, u2elo2]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [hc12, hlam, hphi, p687_1, u2elo2]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [hlam, p687_0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h659, h660, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p687_1, u2elo2]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h0, h545, hc12, hlam, hphi, p687_1, u2elo2]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p687_1, u2elo3]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [hc12, hlam, hphi, p687_1, u2elo3]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h657, hlam, p687_0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [hlam, p687_0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h0, h545, h657, hc12, hlam, hphi, p687_1, u2elo2]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p687_1, u2elo4]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p687_1, u5elo2]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h658, hlam, p687_0]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [h659, hlam, p687_1]
                                · have p687_0 := h687c.1
                                  have p687_1 := h687c.2.1
                                  have p687_2 := h687c.2.2.1
                                  have p687_3 := h687c.2.2.2
                                  linarith only [hlam, p687_0]
                            · linarith only [h0, h490, h659, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h1, h2, h656, h658, hlam]
                        · linarith only [h0, h1, h2, h655, h657, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h655, h656, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h2, h647, h649, h655, hc12, hlam, hphi, u2elo2]
            · linarith only [h647, h648, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h719 | h719
            · rcases m.htr 1 2 3 (by decide) (by decide) with h720 | h720
              · linarith only [h0, h2, h720, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h722 | h722
                · linarith only [h0, h490, h722, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h724 | h724
                  · linarith only [h0, h545, h724, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h726 | h726
                    · linarith only [h1, h647, h726, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h728 | h728
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h729 | h729
                        · linarith only [h545, h647, h719, h729, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h731 | h731
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h732 | h732
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h733 | h733
                              · rcases h2bigk with h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h545, h731, hc12, hlam, hphi, p734_1, u2elo2]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h2, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h490, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h545, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h0, hlam, p734_1]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h720, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h722, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h724, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h729, hc02, hlam, hphi, p734_1, u2elo3]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h729, hc12, hlam, hphi, p734_1, u2elo3]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h729, hlam, p734_1]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h0, h545, h729, hc12, hlam, hphi, p734_1, u2elo3]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, p734_1, u2elo3]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hc12, hlam, hphi, p734_1, u2elo3]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h0, h2, hc12, hlam, hphi, p734_1, u2elo3]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h0, h545, hc12, hlam, hphi, p734_1, u2elo3]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h0, h731, hc12, hlam, hphi, p734_1, u2elo2]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p734_1, u5elo2]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h731, hlam, p734_0]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [h732, hlam, p734_1]
                                · have p734_0 := h734c.1
                                  have p734_1 := h734c.2.1
                                  have p734_2 := h734c.2.2.1
                                  have p734_3 := h734c.2.2.2
                                  linarith only [hlam, p734_0]
                              · linarith only [h729, h733, hc23, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h0, h490, h732, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h0, h2, h731, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h647, h719, h728, hc13, hc34, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h764 | h764
              · linarith only [h0, h545, h764, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h766 | h766
                · linarith only [h0, h2, h719, h766, hc24, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h768 | h768
                  · linarith only [h0, h2, h545, h719, h768, hc05, hlam, hphi, u5elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h770 | h770
                    · linarith only [h1, h719, h770, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h772 | h772
                      · linarith only [h1, h719, h772, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h774 | h774
                        · linarith only [h2, h647, h774, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h776 | h776
                          · linarith only [h0, h2, h719, h776, hc12, hlam, hphi, u2elo2]
                          · linarith only [h0, h2, h776, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h779 | h779
    · linarith only [h0, h1, h779, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h781 | h781
      · rcases m.htr 0 2 5 (by decide) (by decide) with h782 | h782
        · rcases m.htr 0 3 4 (by decide) (by decide) with h783 | h783
          · rcases m.htr 0 3 5 (by decide) (by decide) with h784 | h784
            · rcases m.htr 1 2 3 (by decide) (by decide) with h785 | h785
              · linarith only [h779, h785, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h1, h785, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h784, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h0, h1, h781, h783, hlam]
        · linarith only [h781, h782, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h791 | h791
        · rcases m.htr 0 3 4 (by decide) (by decide) with h792 | h792
          · rcases m.htr 0 3 5 (by decide) (by decide) with h793 | h793
            · rcases m.htr 1 2 3 (by decide) (by decide) with h794 | h794
              · linarith only [h0, h1, h779, h794, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h794, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h793, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h798 | h798
            · rcases m.htr 1 2 3 (by decide) (by decide) with h799 | h799
              · linarith only [h0, h1, h792, h799, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h799, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h798, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h803 | h803
          · rcases m.htr 0 3 5 (by decide) (by decide) with h804 | h804
            · rcases m.htr 1 2 3 (by decide) (by decide) with h805 | h805
              · linarith only [h0, h791, h805, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · linarith only [h0, h1, h805, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h804, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h809 | h809
            · rcases m.htr 1 2 3 (by decide) (by decide) with h810 | h810
              · linarith only [h0, h1, h803, h810, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h810, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h809, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

end R2N4
