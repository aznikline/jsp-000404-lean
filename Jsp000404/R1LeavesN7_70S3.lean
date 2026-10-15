import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_14_25_L_0_L_I_M_LR_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h4, h8, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                    · linarith only [h11, h8, h9, hlam]
                    · rcases h4bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h1, h7, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13_1, u2elo0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        rcases p13_3 (m.d 0 4) (by simp) with h16 | h16
                        · rcases p13_3 (m.d 1 4) (by simp) with h17 | h17
                          · linarith only [h0, h17, hlam]
                          · linarith only [h17, h5, hlam]
                        · linarith only [h1, h16, hlam]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        rcases p13_3 (m.d 0 4) (by simp) with h21 | h21
                        · rcases p13_3 (m.d 1 4) (by simp) with h22 | h22
                          · linarith only [h0, h22, hlam]
                          · linarith only [h22, h6, hlam]
                        · linarith only [h2, h21, hlam]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h1, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13_1, u2elo0]
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
                        rcases p13_3 (m.d 0 4) (by simp) with h29 | h29
                        · rcases p13_3 (m.d 1 4) (by simp) with h30 | h30
                          · rcases p13_3 (m.d 2 4) (by simp) with h31 | h31
                            · linarith only [h31, h5, hlam]
                            · rcases p13_3 (m.d 3 4) (by simp) with h33 | h33
                              · linarith only [h33, h6, hlam]
                              · rcases p13_3 (m.d 4 5) (by simp) with h35 | h35
                                · linarith only [h35, h7, hlam]
                                · linarith only [h35, h9, hlam]
                          · linarith only [h30, h5, hlam]
                        · linarith only [h1, h29, hlam]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        rcases p13_3 (m.d 0 4) (by simp) with h40 | h40
                        · rcases p13_3 (m.d 1 4) (by simp) with h41 | h41
                          · rcases p13_3 (m.d 2 4) (by simp) with h42 | h42
                            · linarith only [h42, h5, hlam]
                            · linarith only [h42, h8, hlam]
                          · linarith only [h41, h6, hlam]
                        · linarith only [h2, h40, hlam]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h0, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p13_1]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h1, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h5, hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h9, hc34, hc45, hlam, hphi, p13_1]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h9, hlam, p13_0]
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
                        linarith only [h11, hlam, p13_0]
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
                        linarith only [hc24, hlam, hphi, ht45, p13_1, u5elo4]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [h0, h1, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13_1, u2elo0]
                      · have p13_0 := h13c.1
                        have p13_1 := h13c.2.1
                        have p13_2 := h13c.2.2.1
                        have p13_3 := h13c.2.2.2
                        linarith only [hlam, p13_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                  · linarith only [h1, h63, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi9]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h65 | h65
                    · linarith only [h4, h6, h63, h65, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h65, h8, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                  · linarith only [h5, h69, h7, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                    · linarith only [h5, h68, h7, h71, hlam]
                    · rcases h4bigk with h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c | h73c
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        rcases p73_3 (m.d 0 4) (by simp) with h75 | h75
                        · rcases p73_3 (m.d 1 4) (by simp) with h76 | h76
                          · linarith only [h0, h76, hlam]
                          · rcases p73_3 (m.d 2 4) (by simp) with h78 | h78
                            · linarith only [h1, h78, hlam]
                            · rcases p73_3 (m.d 3 4) (by simp) with h80 | h80
                              · linarith only [h2, h80, hlam]
                              · rcases p73_3 (m.d 4 5) (by simp) with h82 | h82
                                · linarith only [h3, h82, hlam]
                                · linarith only [h7, h82, hlam]
                        · linarith only [h0, h75, hlam]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        rcases p73_3 (m.d 0 4) (by simp) with h86 | h86
                        · rcases p73_3 (m.d 1 4) (by simp) with h87 | h87
                          · linarith only [h0, h87, hlam]
                          · linarith only [h5, h87, hlam]
                        · linarith only [h1, h86, hlam]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        rcases p73_3 (m.d 0 4) (by simp) with h91 | h91
                        · rcases p73_3 (m.d 1 4) (by simp) with h92 | h92
                          · linarith only [h0, h92, hlam]
                          · linarith only [h6, h92, hlam]
                        · linarith only [h2, h91, hlam]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h1, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p73_1, u2elo0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h0, hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h68, h7, hc34, hc45, hlam, hphi, p73_1]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h1, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p73_1, u2elo0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h7, hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h1, hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h5, hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p73_1, u2elo0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h69, hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h2, hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h6, hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h68, hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h71, hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h3, hlam, p73_0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h1, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p73_1, u2elo0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h1, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p73_1, u2elo0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [h1, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p73_1, u2elo0]
                      · have p73_0 := h73c.1
                        have p73_1 := h73c.2.1
                        have p73_2 := h73c.2.2.1
                        have p73_3 := h73c.2.2.2
                        linarith only [hlam, p73_0]
                · linarith only [h1, h3, h6, h68, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
              · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
                · linarith only [h119, h4, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                  · linarith only [h1, h121, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi9]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
                    · rcases h4bigk with h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c | h124c
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [hlam, p124_0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h1, h118, h119, h121, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p124_1, u2elo0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        rcases p124_3 (m.d 0 4) (by simp) with h127 | h127
                        · rcases p124_3 (m.d 1 4) (by simp) with h128 | h128
                          · linarith only [h0, h128, hlam]
                          · linarith only [h128, h5, hlam]
                        · linarith only [h1, h127, hlam]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h1, h118, h119, h121, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p124_1, u2elo0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h1, h119, h121, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p124_1, u2elo0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h0, hlam, p124_0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [hlam, p124_0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        rcases p124_3 (m.d 0 4) (by simp) with h136 | h136
                        · rcases p124_3 (m.d 1 4) (by simp) with h137 | h137
                          · rcases p124_3 (m.d 2 4) (by simp) with h138 | h138
                            · linarith only [h138, h5, hlam]
                            · rcases p124_3 (m.d 3 4) (by simp) with h140 | h140
                              · rcases p124_3 (m.d 4 5) (by simp) with h141 | h141
                                · linarith only [h118, h141, hlam]
                                · linarith only [h121, h141, hlam]
                              · linarith only [h119, h140, hlam]
                          · linarith only [h137, h5, hlam]
                        · linarith only [h1, h136, hlam]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h6, hlam, p124_1]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h119, h121, h6, hc23, hc34, hlam, hphi, p124_1]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h1, hlam, p124_0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h5, hlam, p124_0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [hlam, p124_0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h119, hlam, p124_1]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h121, hlam, p124_0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h2, hlam, p124_0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h1, h118, h119, h121, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p124_1, u2elo0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        rcases p124_3 (m.d 0 4) (by simp) with h156 | h156
                        · rcases p124_3 (m.d 1 4) (by simp) with h157 | h157
                          · linarith only [h157, h6, hlam]
                          · linarith only [h157, h5, hlam]
                        · linarith only [h1, h156, hlam]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [hlam, p124_0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h1, h119, h121, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p124_1, u2elo0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h3, hlam, p124_0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h118, hlam, p124_0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h119, hc23, hlam, hphi, ht34, ht45, p124_1, u5elo4]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [h123, hlam, p124_0]
                      · have p124_0 := h124c.1
                        have p124_1 := h124c.2.1
                        have p124_2 := h124c.2.2.1
                        have p124_3 := h124c.2.2.2
                        linarith only [hlam, p124_0]
                    · linarith only [h118, h123, h6, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                · linarith only [h1, h118, h169, h3, h4, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h171 | h171
                  · linarith only [h1, h118, h171, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h173 | h173
                    · rcases h4bigk with h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [hlam, p174_0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        rcases p174_3 (m.d 0 4) (by simp) with h176 | h176
                        · rcases p174_3 (m.d 1 4) (by simp) with h177 | h177
                          · linarith only [h0, h177, hlam]
                          · rcases p174_3 (m.d 2 4) (by simp) with h179 | h179
                            · linarith only [h1, h179, hlam]
                            · rcases p174_3 (m.d 3 4) (by simp) with h181 | h181
                              · linarith only [h181, h2, hlam]
                              · linarith only [h181, h6, hlam]
                        · linarith only [h0, h176, hlam]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        rcases p174_3 (m.d 0 4) (by simp) with h185 | h185
                        · rcases p174_3 (m.d 1 4) (by simp) with h186 | h186
                          · linarith only [h0, h186, hlam]
                          · linarith only [h186, h5, hlam]
                        · linarith only [h1, h185, hlam]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h1, h118, h173, h4, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p174_1, u2elo0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h1, h118, h4, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p174_1, u2elo0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h0, hlam, p174_0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [hlam, p174_0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h118, h173, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p174_1]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h6, hlam, p174_1]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h118, hlam, p174_0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h1, hlam, p174_0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h5, hlam, p174_0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [hlam, p174_0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h169, hlam, p174_1]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h171, hlam, p174_0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h2, hlam, p174_0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        rcases p174_3 (m.d 0 4) (by simp) with h203 | h203
                        · rcases p174_3 (m.d 1 4) (by simp) with h204 | h204
                          · linarith only [h204, h6, hlam]
                          · rcases p174_3 (m.d 2 4) (by simp) with h206 | h206
                            · linarith only [h169, h206, hlam]
                            · rcases p174_3 (m.d 3 4) (by simp) with h208 | h208
                              · rcases p174_3 (m.d 4 5) (by simp) with h209 | h209
                                · linarith only [h173, h209, hlam]
                                · linarith only [h118, h209, hlam]
                              · linarith only [h208, h6, hlam]
                        · linarith only [h0, h203, hlam]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        rcases p174_3 (m.d 0 4) (by simp) with h214 | h214
                        · rcases p174_3 (m.d 1 4) (by simp) with h215 | h215
                          · linarith only [h215, h6, hlam]
                          · linarith only [h215, h5, hlam]
                        · linarith only [h1, h214, hlam]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [hlam, p174_0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h1, h118, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, p174_1, u2elo0, u5ehi6]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h3, hlam, p174_0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, p174_1, u5elo4]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h1, h169, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p174_1, u2elo0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [h173, hlam, p174_0]
                      · have p174_0 := h174c.1
                        have p174_1 := h174c.2.1
                        have p174_2 := h174c.2.2.1
                        have p174_3 := h174c.2.2.2
                        linarith only [hlam, p174_0]
                    · linarith only [h1, h173, h3, h4, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h1, h5, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h228 | h228
          · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
            · rcases m.htr 1 4 5 (by decide) (by decide) with h230 | h230
              · linarith only [h228, h230, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
                · rcases m.htr 2 4 5 (by decide) (by decide) with h233 | h233
                  · linarith only [h228, h230, h233, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h235 | h235
                    · linarith only [h228, h230, h232, h235, hlam]
                    · rcases h4bigk with h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        rcases p237_3 (m.d 0 4) (by simp) with h239 | h239
                        · rcases p237_3 (m.d 1 4) (by simp) with h240 | h240
                          · linarith only [h0, h240, hlam]
                          · rcases p237_3 (m.d 2 4) (by simp) with h242 | h242
                            · linarith only [h1, h242, hlam]
                            · rcases p237_3 (m.d 3 4) (by simp) with h244 | h244
                              · linarith only [h2, h244, hlam]
                              · rcases p237_3 (m.d 4 5) (by simp) with h246 | h246
                                · linarith only [h246, h3, hlam]
                                · linarith only [h230, h246, hlam]
                        · linarith only [h0, h239, hlam]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        rcases p237_3 (m.d 0 4) (by simp) with h250 | h250
                        · rcases p237_3 (m.d 1 4) (by simp) with h251 | h251
                          · linarith only [h0, h251, hlam]
                          · linarith only [h228, h251, hlam]
                        · linarith only [h1, h250, hlam]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        rcases p237_3 (m.d 0 4) (by simp) with h255 | h255
                        · rcases p237_3 (m.d 1 4) (by simp) with h256 | h256
                          · linarith only [h0, h256, hlam]
                          · linarith only [h229, h256, hlam]
                        · linarith only [h2, h255, hlam]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h1, h230, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p237_1, u2elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h0, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h230, h232, hc34, hc45, hlam, hphi, p237_1]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h1, h230, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p237_1, u2elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h230, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h1, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h228, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p237_1, u2elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h233, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h2, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h229, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h232, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h235, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h3, hlam, p237_0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h1, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p237_1, u2elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h1, h232, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p237_1, u2elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [h1, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p237_1, u2elo0]
                      · have p237_0 := h237c.1
                        have p237_1 := h237c.2.1
                        have p237_2 := h237c.2.2.1
                        have p237_3 := h237c.2.2.2
                        linarith only [hlam, p237_0]
                · linarith only [h1, h2, h232, h4, hc12, hlam, hphi, u2elo0]
            · linarith only [h228, h229, h4, hlam]
          · linarith only [h1, h228, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h284 | h284
        · rcases m.htr 1 2 4 (by decide) (by decide) with h285 | h285
          · rcases m.htr 1 3 4 (by decide) (by decide) with h286 | h286
            · rcases m.htr 1 4 5 (by decide) (by decide) with h287 | h287
              · linarith only [h0, h287, h3, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h289 | h289
                · rcases m.htr 2 4 5 (by decide) (by decide) with h290 | h290
                  · linarith only [h0, h285, h290, h3, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h292 | h292
                    · linarith only [h284, h289, h292, h3, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases h4bigk with h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c | h294c
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h285, h289, h3, hc34, hc45, hlam, hphi, p294_1]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h289, h3, hc34, hlam, hphi, ht45, p294_1, u5elo4]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h3, hc34, hlam, hphi, ht45, p294_1, u5elo4]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h3, hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h0, hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h0, h289, h3, hc34, hlam, hphi, ht45, p294_1, u5elo4]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h0, h3, hc34, hlam, hphi, ht45, p294_1, u5elo4]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h287, hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h1, hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h285, hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p294_1, u2elo0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h290, hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h2, hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h286, hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h289, hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h292, hlam, p294_0]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [hc04, hlam, hphi, ht45, p294_1, u5elo4]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h285, hc24, hlam, hphi, ht45, p294_1, u5elo4]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [h289, hc34, hlam, hphi, ht45, p294_1, u5elo4]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [hc34, hlam, hphi, ht45, p294_1, u5elo4]
                      · have p294_0 := h294c.1
                        have p294_1 := h294c.2.1
                        have p294_2 := h294c.2.2.1
                        have p294_3 := h294c.2.2.2
                        linarith only [hlam, p294_0]
                · linarith only [h2, h289, h3, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h2, h286, h3, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h1, h285, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h323 | h323
          · rcases m.htr 1 3 4 (by decide) (by decide) with h324 | h324
            · rcases m.htr 1 4 5 (by decide) (by decide) with h325 | h325
              · linarith only [h0, h3, h325, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h327 | h327
                · rcases m.htr 2 4 5 (by decide) (by decide) with h328 | h328
                  · linarith only [h284, h3, h323, h328, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h330 | h330
                    · linarith only [h0, h3, h323, h327, h330, hlam]
                    · rcases h4bigk with h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h3, h323, h327, hc34, hc45, hlam, hphi, p332_1]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h3, h327, hc34, hlam, hphi, ht45, p332_1, u5elo4]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h3, hc34, hlam, hphi, ht45, p332_1, u5elo4]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h3, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h0, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h0, h3, h327, hc34, hlam, hphi, ht45, p332_1, u5elo4]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h0, h3, hc34, hlam, hphi, ht45, p332_1, u5elo4]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h325, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h1, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h323, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p332_1, u2elo0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h328, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h2, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h324, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h327, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h330, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hc04, hlam, hphi, ht45, p332_1, u5elo4]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h323, hc24, hlam, hphi, ht45, p332_1, u5elo4]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h327, hc34, hlam, hphi, ht45, p332_1, u5elo4]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hc34, hlam, hphi, ht45, p332_1, u5elo4]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hlam, p332_0]
                · linarith only [h2, h284, h3, h327, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h2, h3, h324, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h1, h323, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h361 | h361
      · rcases m.htr 1 2 3 (by decide) (by decide) with h362 | h362
        · rcases m.htr 1 2 4 (by decide) (by decide) with h363 | h363
          · rcases m.htr 1 3 4 (by decide) (by decide) with h364 | h364
            · linarith only [h2, h361, h362, h364, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h366 | h366
              · rcases m.htr 2 3 4 (by decide) (by decide) with h367 | h367
                · linarith only [h0, h2, h366, h367, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h369 | h369
                  · linarith only [h1, h369, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi9]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h371 | h371
                    · rcases h4bigk with h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h366, h367, h369, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        rcases p372_3 (m.d 0 4) (by simp) with h375 | h375
                        · rcases p372_3 (m.d 1 4) (by simp) with h376 | h376
                          · linarith only [h0, h376, hlam]
                          · linarith only [h363, h376, hlam]
                        · linarith only [h1, h375, hlam]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h2, hlam, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h1, h367, h369, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p372_1, u2elo0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h0, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        rcases p372_3 (m.d 0 4) (by simp) with h384 | h384
                        · rcases p372_3 (m.d 1 4) (by simp) with h385 | h385
                          · rcases p372_3 (m.d 2 4) (by simp) with h386 | h386
                            · linarith only [h363, h386, hlam]
                            · rcases p372_3 (m.d 3 4) (by simp) with h388 | h388
                              · rcases p372_3 (m.d 4 5) (by simp) with h389 | h389
                                · linarith only [h366, h389, hlam]
                                · linarith only [h369, h389, hlam]
                              · linarith only [h367, h388, hlam]
                          · linarith only [h363, h385, hlam]
                        · linarith only [h1, h384, hlam]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h364, hlam, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h0, h367, h369, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h1, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h363, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h367, hlam, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h369, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h361, h367, h369, hc23, hc34, hlam, hphi, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h366, h367, h369, hc23, hc34, hlam, hphi, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        rcases p372_3 (m.d 0 4) (by simp) with h404 | h404
                        · linarith only [h2, h404, hlam]
                        · linarith only [h1, h404, hlam]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h367, h369, hc23, hc34, hlam, hphi, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h361, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h366, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h361, h367, hc23, hlam, hphi, ht34, ht45, p372_1, u5elo0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h371, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [hlam, p372_0]
                    · linarith only [h0, h1, h364, h366, h371, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
                · linarith only [h2, h361, h366, h415, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h417 | h417
                  · linarith only [h1, h362, h364, h366, h417, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h419 | h419
                    · rcases h4bigk with h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [hlam, p420_0]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        rcases p420_3 (m.d 0 4) (by simp) with h422 | h422
                        · rcases p420_3 (m.d 1 4) (by simp) with h423 | h423
                          · linarith only [h0, h423, hlam]
                          · rcases p420_3 (m.d 2 4) (by simp) with h425 | h425
                            · linarith only [h1, h425, hlam]
                            · rcases p420_3 (m.d 3 4) (by simp) with h427 | h427
                              · rcases p420_3 (m.d 4 5) (by simp) with h428 | h428
                                · linarith only [h361, h428, hlam]
                                · linarith only [h366, h428, hlam]
                              · linarith only [h364, h427, hlam]
                        · linarith only [h0, h422, hlam]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        rcases p420_3 (m.d 0 4) (by simp) with h433 | h433
                        · rcases p420_3 (m.d 1 4) (by simp) with h434 | h434
                          · linarith only [h0, h434, hlam]
                          · linarith only [h363, h434, hlam]
                        · linarith only [h1, h433, hlam]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h2, hlam, p420_1]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h2, h362, h364, h366, hc23, hc34, hlam, hphi, p420_1]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h0, hlam, p420_0]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [hlam, p420_0]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h366, hc24, hc45, hlam, hphi, p420_1]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h364, hlam, p420_1]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h366, hlam, p420_0]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h1, hlam, p420_0]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h363, hlam, p420_0]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [hlam, p420_0]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h415, hlam, p420_1]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h417, hlam, p420_0]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h361, h366, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p420_1]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        rcases p420_3 (m.d 0 4) (by simp) with h451 | h451
                        · linarith only [h2, h451, hlam]
                        · linarith only [h0, h451, hlam]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        rcases p420_3 (m.d 0 4) (by simp) with h454 | h454
                        · linarith only [h2, h454, hlam]
                        · linarith only [h1, h454, hlam]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [hlam, p420_0]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h362, h364, h366, hc23, hc34, hlam, hphi, p420_1]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h361, hlam, p420_0]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h362, h364, hc23, hlam, hphi, ht34, ht45, p420_1, u5elo4]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h1, h361, h415, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p420_1, u2elo0]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [h419, hlam, p420_0]
                      · have p420_0 := h420c.1
                        have p420_1 := h420c.2.1
                        have p420_2 := h420c.2.2.1
                        have p420_3 := h420c.2.2.2
                        linarith only [hlam, p420_0]
                    · linarith only [h1, h2, h361, h419, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h1, h363, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h466 | h466
          · rcases m.htr 1 3 4 (by decide) (by decide) with h467 | h467
            · linarith only [h2, h361, h362, h467, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
            · linarith only [h362, h466, h467, hlam]
          · linarith only [h1, h466, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
        · rcases m.htr 1 2 4 (by decide) (by decide) with h472 | h472
          · rcases m.htr 1 3 4 (by decide) (by decide) with h473 | h473
            · linarith only [h0, h2, h361, h473, hc03, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h475 | h475
              · linarith only [h0, h361, h475, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                · linarith only [h471, h473, h477, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h479 | h479
                  · linarith only [h0, h361, h472, h479, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h481 | h481
                    · rcases h4bigk with h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [hlam, p482_0]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h361, h481, hc14, hlam, hphi, ht45, p482_1, u5elo3]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h361, h481, hc24, hlam, hphi, ht45, p482_1, u5elo3]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h2, hlam, p482_1]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h361, hlam, p482_0]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h0, hlam, p482_0]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [hlam, p482_0]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h0, h361, h481, hc24, hlam, hphi, ht45, p482_1, u5elo3]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h473, hlam, p482_1]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h475, hlam, p482_0]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h1, hlam, p482_0]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h472, hlam, p482_0]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [hlam, p482_0]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h477, hlam, p482_1]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h479, hlam, p482_0]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        rcases p482_3 (m.d 0 4) (by simp) with h498 | h498
                        · linarith only [h2, h498, hlam]
                        · rcases p482_3 (m.d 1 4) (by simp) with h500 | h500
                          · linarith only [h473, h500, hlam]
                          · rcases p482_3 (m.d 2 4) (by simp) with h502 | h502
                            · linarith only [h477, h502, hlam]
                            · rcases p482_3 (m.d 3 4) (by simp) with h504 | h504
                              · rcases p482_3 (m.d 4 5) (by simp) with h505 | h505
                                · linarith only [h481, h505, hlam]
                                · linarith only [h361, h505, hlam]
                              · linarith only [h2, h504, hlam]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        rcases p482_3 (m.d 0 4) (by simp) with h509 | h509
                        · linarith only [h2, h509, hlam]
                        · linarith only [h0, h509, hlam]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        rcases p482_3 (m.d 0 4) (by simp) with h512 | h512
                        · linarith only [h2, h512, hlam]
                        · linarith only [h1, h512, hlam]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [hlam, p482_0]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h1, h361, h477, hc23, hc34, hlam, hphi, p482_1]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h0, h481, hc14, hlam, hphi, ht45, p482_1, u5elo3]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h472, h477, h481, hc23, hlam, hphi, ht34, ht45, p482_1, u5elo3]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h477, h481, hc23, hlam, hphi, ht34, ht45, p482_1, u5elo3]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [h481, hlam, p482_0]
                      · have p482_0 := h482c.1
                        have p482_1 := h482c.2.1
                        have p482_2 := h482c.2.2.1
                        have p482_3 := h482c.2.2.2
                        linarith only [hlam, p482_0]
                    · linarith only [h2, h481, hc03, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h1, h472, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h524 | h524
          · rcases m.htr 1 3 4 (by decide) (by decide) with h525 | h525
            · linarith only [h0, h2, h361, h525, hc03, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h0, h361, h471, h524, h525, hc24, hlam, hphi, ht45, u5elo4]
          · linarith only [h1, h524, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h529 | h529
    · rcases m.htr 0 4 5 (by decide) (by decide) with h530 | h530
      · rcases m.htr 1 2 3 (by decide) (by decide) with h531 | h531
        · rcases m.htr 1 2 4 (by decide) (by decide) with h532 | h532
          · linarith only [h1, h532, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h534 | h534
            · linarith only [h531, h532, h534, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h536 | h536
              · rcases m.htr 2 3 4 (by decide) (by decide) with h537 | h537
                · linarith only [h531, h532, h534, h537, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1, h529, h537, hlam]
              · linarith only [h1, h530, h532, h536, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h541 | h541
          · linarith only [h1, h530, h531, h541, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h543 | h543
            · rcases m.htr 1 4 5 (by decide) (by decide) with h544 | h544
              · rcases m.htr 2 3 4 (by decide) (by decide) with h545 | h545
                · rcases m.htr 2 4 5 (by decide) (by decide) with h546 | h546
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h547 | h547
                    · linarith only [h531, h543, h547, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                    · rcases h4bigk with h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c | h549c
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [hlam, p549_0]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h529, h544, h547, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p549_1]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h1, hlam, p549_1]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        rcases p549_3 (m.d 0 4) (by simp) with h553 | h553
                        · rcases p549_3 (m.d 1 4) (by simp) with h554 | h554
                          · linarith only [h0, h554, hlam]
                          · linarith only [h543, h554, hlam]
                        · linarith only [h529, h553, hlam]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h1, h545, h547, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p549_1, u2elo2]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h0, hlam, p549_0]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [hlam, p549_0]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h541, hlam, p549_1]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        rcases p549_3 (m.d 0 4) (by simp) with h562 | h562
                        · rcases p549_3 (m.d 1 4) (by simp) with h563 | h563
                          · rcases p549_3 (m.d 2 4) (by simp) with h564 | h564
                            · rcases p549_3 (m.d 3 4) (by simp) with h565 | h565
                              · linarith only [h543, h565, hlam]
                              · rcases p549_3 (m.d 4 5) (by simp) with h567 | h567
                                · linarith only [h544, h567, hlam]
                                · linarith only [h547, h567, hlam]
                            · linarith only [h545, h564, hlam]
                          · linarith only [h543, h563, hlam]
                        · linarith only [h529, h562, hlam]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h0, h547, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p549_1]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h1, h545, hc02, hlam, hphi, p549_1, u2elo2]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h541, h545, hc12, hlam, hphi, p549_1, u2elo2]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [hlam, p549_0]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        rcases p549_3 (m.d 0 4) (by simp) with h577 | h577
                        · linarith only [h1, h577, hlam]
                        · linarith only [h529, h577, hlam]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h545, h547, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p549_1, u2elo2]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h529, hlam, p549_0]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h543, hlam, p549_0]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h545, hlam, p549_0]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [hlam, p549_0]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h547, hlam, p549_0]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h530, hlam, p549_0]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h544, hlam, p549_0]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [h546, hlam, p549_0]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [hc34, hlam, hphi, ht45, p549_1, u5elo4]
                      · have p549_0 := h549c.1
                        have p549_1 := h549c.2.1
                        have p549_2 := h549c.2.2.1
                        have p549_3 := h549c.2.2.2
                        linarith only [hlam, p549_0]
                  · linarith only [h0, h1, h544, h546, hlam]
                · linarith only [h1, h529, h531, h545, hc12, hlam, hphi, u2elo3]
              · linarith only [h1, h530, h541, h544, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h594 | h594
              · rcases m.htr 2 3 4 (by decide) (by decide) with h595 | h595
                · linarith only [h543, h594, h595, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                · linarith only [h1, h529, h531, h595, hc12, hlam, hphi, u2elo3]
              · linarith only [h1, h530, h541, h594, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h599 | h599
        · rcases m.htr 1 2 4 (by decide) (by decide) with h600 | h600
          · linarith only [h1, h600, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h530, h599, h600, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h603 | h603
          · linarith only [h1, h599, h603, hc02, hlam, hphi, u2elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h605 | h605
            · rcases m.htr 1 4 5 (by decide) (by decide) with h606 | h606
              · linarith only [h0, h530, h606, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h608 | h608
                · rcases m.htr 2 4 5 (by decide) (by decide) with h609 | h609
                  · linarith only [h0, h530, h603, h609, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1, h609, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h529, h530, h608, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h529, h530, h605, hc13, hlam, hphi, ht34, ht45, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h614 | h614
      · rcases m.htr 1 2 3 (by decide) (by decide) with h615 | h615
        · rcases m.htr 1 2 4 (by decide) (by decide) with h616 | h616
          · linarith only [h1, h614, h616, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h618 | h618
            · linarith only [h529, h614, h615, h616, h618, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi9]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h620 | h620
              · rcases m.htr 2 3 4 (by decide) (by decide) with h621 | h621
                · linarith only [h0, h529, h620, h621, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h623 | h623
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h624 | h624
                    · rcases h4bigk with h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h620, hc04, hlam, hphi, ht0b, ht5b, p625_1, u5ehi9]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h1, hlam, p625_1]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h529, hlam, p625_1]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, p625_1, u2elo3, u5ehi9]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h0, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h616, hlam, p625_1]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h618, hlam, p625_1]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p625_1, u5ehi9]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h1, hc02, hlam, hphi, p625_1, u2elo3]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h616, hc12, hlam, hphi, p625_1, u2elo3]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h621, hlam, p625_1]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p625_1, u2elo3, u5ehi9]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h0, h620, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p625_1, u5ehi9]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h620, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p625_1, u5ehi9]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h1, hc02, hc34, hlam, hphi, ht23, p625_1]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        rcases p625_3 (m.d 0 4) (by simp) with h645 | h645
                        · linarith only [h529, h645, hlam]
                        · linarith only [h614, h645, hlam]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h614, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h620, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h623, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h624, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [hlam, p625_0]
                    · linarith only [h529, h624, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h1, h620, h623, hlam]
              · linarith only [h1, h614, h615, h616, h620, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h656 | h656
          · linarith only [h1, h614, h615, h656, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h658 | h658
            · linarith only [h529, h614, h615, h658, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h660 | h660
              · rcases m.htr 2 3 4 (by decide) (by decide) with h661 | h661
                · linarith only [h615, h658, h661, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h663 | h663
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h664 | h664
                    · rcases h4bigk with h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h660, hc04, hlam, hphi, ht0b, ht5b, p665_1, u5ehi9]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h1, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h529, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, p665_1, u2elo3, u5ehi9]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h0, hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h656, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h658, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p665_1, u5ehi9]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h1, hc02, hlam, hphi, p665_1, u2elo3]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h656, hc12, hlam, hphi, p665_1, u2elo3]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h661, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p665_1, u2elo3, u5ehi9]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h0, h660, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p665_1, u5ehi9]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h660, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p665_1, u5ehi9]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h1, hc02, hc34, hlam, hphi, ht23, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        rcases p665_3 (m.d 0 4) (by simp) with h685 | h685
                        · linarith only [h529, h685, hlam]
                        · linarith only [h614, h685, hlam]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h614, hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h660, hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h663, hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h664, hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [hlam, p665_0]
                    · linarith only [h0, h1, h529, h660, h664, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1, h660, h663, hlam]
              · linarith only [h1, h614, h656, h660, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h696 | h696
        · rcases m.htr 1 2 4 (by decide) (by decide) with h697 | h697
          · linarith only [h1, h697, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h614, h696, h697, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h700 | h700
          · linarith only [h1, h696, h700, hc02, hlam, hphi, u2elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h702 | h702
            · linarith only [h0, h529, h614, h702, hc03, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h704 | h704
              · linarith only [h0, h614, h704, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h706 | h706
                · linarith only [h696, h702, h706, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h708 | h708
                  · linarith only [h1, h614, h708, hc02, hlam, hphi, u2elo3]
                  · linarith only [h1, h708, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]

end R2N4
