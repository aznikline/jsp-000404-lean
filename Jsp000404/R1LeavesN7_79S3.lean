import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_23_L_R_L_I_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h11, h14, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h11, h13, h14, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                              · linarith only [h13, h17, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                              · rcases h2bigk with h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h0, h12, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p19_1]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  rcases p19_3 (m.d 0 2) (by simp) with h22 | h22
                                  · rcases p19_3 (m.d 1 2) (by simp) with h23 | h23
                                    · linarith only [h0, h23, hlam]
                                    · linarith only [h23, h7, hlam]
                                  · linarith only [h22, hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  rcases p19_3 (m.d 0 2) (by simp) with h27 | h27
                                  · rcases p19_3 (m.d 1 2) (by simp) with h28 | h28
                                    · linarith only [h0, h28, hlam]
                                    · linarith only [h28, h8, hlam]
                                  · linarith only [h27, hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  rcases p19_3 (m.d 0 2) (by simp) with h32 | h32
                                  · rcases p19_3 (m.d 1 2) (by simp) with h33 | h33
                                    · linarith only [h0, h33, hlam]
                                    · linarith only [h33, h9, hlam]
                                  · linarith only [h32, hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h0, hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h0, h12, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19_1]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  rcases p19_3 (m.d 0 2) (by simp) with h40 | h40
                                  · rcases p19_3 (m.d 1 2) (by simp) with h41 | h41
                                    · rcases p19_3 (m.d 2 3) (by simp) with h42 | h42
                                      · linarith only [h42, h7, hlam]
                                      · linarith only [h11, h42, hlam]
                                    · linarith only [h41, hlam, p19_0]
                                  · linarith only [h3, h40, hlam]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  rcases p19_3 (m.d 0 2) (by simp) with h47 | h47
                                  · rcases p19_3 (m.d 1 2) (by simp) with h48 | h48
                                    · rcases p19_3 (m.d 2 3) (by simp) with h49 | h49
                                      · linarith only [h49, h7, hlam]
                                      · linarith only [h12, h49, hlam]
                                    · linarith only [h48, hlam, p19_0]
                                  · linarith only [h4, h47, hlam]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h2, hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h7, hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h0, h11, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19_1]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h0, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p19_1]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h3, hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h8, hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h11, hlam, p19_1]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h13, hlam, p19_1]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h4, hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h9, hlam, p19_0]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h12, hlam, p19_1]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [h0, h11, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p19_1]
                                · have p19_0 := h19c.1
                                  have p19_1 := h19c.2.1
                                  have p19_2 := h19c.2.2.1
                                  have p19_3 := h19c.2.2.2
                                  linarith only [hlam, p19_0]
                          · linarith only [h12, h6, hc23, hlam, hphi, u3elo0]
                        · linarith only [h11, h5, hc23, hlam, hphi, u3elo0]
                      · linarith only [h10, h5, hc13, hlam, hphi, u3elo0]
                    · linarith only [h4, h6, h7, h9, hc23, hlam, hphi, u3elo0]
                  · linarith only [h3, h5, h7, h8, hc23, hlam, hphi, u3elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h74 | h74
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h78 | h78
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h79 | h79
                            · linarith only [h7, h74, h79, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
                              · linarith only [h77, h79, h81, hlam]
                              · rcases h2bigk with h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c | h83c
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [hlam, p83_0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  rcases p83_3 (m.d 0 2) (by simp) with h85 | h85
                                  · rcases p83_3 (m.d 1 2) (by simp) with h86 | h86
                                    · linarith only [h0, h86, hlam]
                                    · rcases p83_3 (m.d 2 3) (by simp) with h88 | h88
                                      · linarith only [h2, h88, hlam]
                                      · linarith only [h7, h88, hlam]
                                  · linarith only [h0, h85, hlam]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h0, h7, h75, h77, h79, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p83_1]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h2, h7, h75, h79, hlam, p83_2]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h2, h7, h75, hlam, p83_2]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h0, hlam, p83_0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [hlam, p83_0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h7, hlam, p83_0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h2, h7, h77, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p83_1, u3elo0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h2, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p83_1, u3elo0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h2, hlam, p83_0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h2, hc12, hlam, hphi, ht23, p83_1, u3elo0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [hlam, p83_0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  rcases p83_3 (m.d 0 2) (by simp) with h103 | h103
                                  · rcases p83_3 (m.d 1 2) (by simp) with h104 | h104
                                    · linarith only [h104, h7, hlam]
                                    · linarith only [h104, h74, hlam]
                                  · linarith only [h103, h3, hlam]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  rcases p83_3 (m.d 0 2) (by simp) with h108 | h108
                                  · rcases p83_3 (m.d 1 2) (by simp) with h109 | h109
                                    · linarith only [h109, h7, hlam]
                                    · linarith only [h109, h75, hlam]
                                  · linarith only [h108, h4, hlam]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h3, hlam, p83_0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h74, hlam, p83_0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h77, hlam, p83_1]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [hlam, p83_0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h79, hlam, p83_1]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h4, hlam, p83_0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h75, hlam, p83_0]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h78, hlam, p83_1]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [h7, h75, h77, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p83_1, u3elo1]
                                · have p83_0 := h83c.1
                                  have p83_1 := h83c.2.1
                                  have p83_2 := h83c.2.2.1
                                  have p83_3 := h83c.2.2.2
                                  linarith only [hlam, p83_0]
                          · linarith only [h7, h78, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h7, h74, h77, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h5, h76, hc13, hlam, hphi, u3elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h128 | h128
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h129 | h129
                            · linarith only [h128, h129, h2, h74, h75, hc02, hc45, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
                              · linarith only [h127, h129, h131, h74, h75, hlam]
                              · rcases h2bigk with h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [hlam, p133_0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  rcases p133_3 (m.d 0 2) (by simp) with h135 | h135
                                  · rcases p133_3 (m.d 1 2) (by simp) with h136 | h136
                                    · linarith only [h0, h136, hlam]
                                    · rcases p133_3 (m.d 2 3) (by simp) with h138 | h138
                                      · linarith only [h138, h2, hlam]
                                      · linarith only [h138, h7, hlam]
                                  · linarith only [h0, h135, hlam]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h128, h74, h75, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p133_1]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h128, h2, h74, h75, hlam, p133_2]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h127, h74, h75, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p133_1]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h0, hlam, p133_0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [hlam, p133_0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h7, hlam, p133_0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h127, h128, h2, h75, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p133_1, u3elo0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h75, hlam, p133_0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h2, hlam, p133_0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h2, hc12, hlam, hphi, ht23, p133_1, u3elo0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [hlam, p133_0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  rcases p133_3 (m.d 0 2) (by simp) with h153 | h153
                                  · rcases p133_3 (m.d 1 2) (by simp) with h154 | h154
                                    · linarith only [h154, h7, hlam]
                                    · linarith only [h154, h74, hlam]
                                  · linarith only [h153, h3, hlam]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h127, h2, h74, h75, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p133_1, u3elo0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h3, hlam, p133_0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h74, hlam, p133_0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h127, hlam, p133_1]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [hlam, p133_0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h129, hlam, p133_1]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h4, hlam, p133_0]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h127, h129, h74, hc34, hc45, hlam, hphi, p133_1]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [h128, hlam, p133_1]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  rcases p133_3 (m.d 0 2) (by simp) with h167 | h167
                                  · rcases p133_3 (m.d 1 2) (by simp) with h168 | h168
                                    · linarith only [h168, h75, hlam]
                                    · linarith only [h168, h74, hlam]
                                  · linarith only [h167, h3, hlam]
                                · have p133_0 := h133c.1
                                  have p133_1 := h133c.2.1
                                  have p133_2 := h133c.2.2.1
                                  have p133_3 := h133c.2.2.2
                                  linarith only [hlam, p133_0]
                          · linarith only [h128, h6, hc23, hlam, hphi, u3elo0]
                        · linarith only [h127, h7, h74, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h126, h5, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h176 | h176
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h177 | h177
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h178 | h178
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h181 | h181
                              · rcases h2bigk with h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  rcases p182_3 (m.d 0 2) (by simp) with h184 | h184
                                  · rcases p182_3 (m.d 1 2) (by simp) with h185 | h185
                                    · linarith only [h0, h185, hlam]
                                    · rcases p182_3 (m.d 2 3) (by simp) with h187 | h187
                                      · linarith only [h187, h2, hlam]
                                      · linarith only [h187, h7, hlam]
                                  · linarith only [h0, h184, hlam]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h0, h176, h179, h181, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h0, h176, h179, h181, h74, hc01, hc45, hlam, hphi, ht0b, ht5b, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h176, h3, h74, hlam, p182_2]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h0, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h7, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h74, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h179, h181, h3, h74, hc02, hc45, hlam, hphi, ht0b, ht5b, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h2, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p182_1, u3elo2]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h176, h179, h181, h2, h74, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p182_1, u3elo0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  rcases p182_3 (m.d 0 2) (by simp) with h203 | h203
                                  · rcases p182_3 (m.d 1 2) (by simp) with h204 | h204
                                    · linarith only [h204, h7, hlam]
                                    · linarith only [h176, h204, hlam]
                                  · linarith only [h203, h4, hlam]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h3, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h0, h176, h179, h181, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h178, hlam, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  rcases p182_3 (m.d 0 2) (by simp) with h212 | h212
                                  · rcases p182_3 (m.d 1 2) (by simp) with h213 | h213
                                    · linarith only [h213, h74, hlam]
                                    · linarith only [h176, h213, hlam]
                                  · linarith only [h212, h4, hlam]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h4, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h176, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h179, hlam, p182_1]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [h180, hlam, p182_0]
                                · have p182_0 := h182c.1
                                  have p182_1 := h182c.2.1
                                  have p182_2 := h182c.2.2.1
                                  have p182_3 := h182c.2.2.2
                                  linarith only [hlam, p182_0]
                              · linarith only [h176, h180, h181, h2, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · linarith only [h176, h180, h74, hlam]
                          · linarith only [h179, h6, hc23, hlam, hphi, u3elo0]
                        · linarith only [h178, h7, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h176, h177, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h229 | h229
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h230 | h230
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h231 | h231
                              · rcases h2bigk with h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  rcases p232_3 (m.d 0 2) (by simp) with h234 | h234
                                  · rcases p232_3 (m.d 1 2) (by simp) with h235 | h235
                                    · linarith only [h0, h235, hlam]
                                    · rcases p232_3 (m.d 2 3) (by simp) with h237 | h237
                                      · linarith only [h2, h237, hlam]
                                      · linarith only [h237, h7, hlam]
                                  · linarith only [h0, h234, hlam]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h0, h227, h231, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p232_1]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  rcases p232_3 (m.d 0 2) (by simp) with h242 | h242
                                  · rcases p232_3 (m.d 1 2) (by simp) with h243 | h243
                                    · linarith only [h0, h243, hlam]
                                    · rcases p232_3 (m.d 2 3) (by simp) with h245 | h245
                                      · linarith only [h2, h245, hlam]
                                      · linarith only [h228, h245, hlam]
                                  · linarith only [h242, hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  rcases p232_3 (m.d 0 2) (by simp) with h249 | h249
                                  · rcases p232_3 (m.d 1 2) (by simp) with h250 | h250
                                    · linarith only [h0, h250, hlam]
                                    · rcases p232_3 (m.d 2 3) (by simp) with h252 | h252
                                      · linarith only [h2, h252, hlam]
                                      · linarith only [h229, h252, hlam]
                                  · linarith only [h249, hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h0, hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h7, hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h74, hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h176, hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h2, hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p232_1, u3elo2]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h176, h2, h230, hc12, hlam, hphi, ht23, p232_1, u3elo0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h176, h2, hc12, hlam, hphi, ht23, p232_1, u3elo0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h3, hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h3, h5, hc12, hlam, hphi, ht23, p232_1, u3elo0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h228, hlam, p232_1]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h176, h3, h5, hc12, hlam, hphi, ht23, p232_1, u3elo0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h4, hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h4, h6, hc12, hlam, hphi, ht23, p232_1, u3elo0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h229, hlam, p232_1]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [h230, hlam, p232_0]
                                · have p232_0 := h232c.1
                                  have p232_1 := h232c.2.1
                                  have p232_2 := h232c.2.2.1
                                  have p232_3 := h232c.2.2.2
                                  linarith only [hlam, p232_0]
                              · rcases h2bigk with h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  rcases p276_3 (m.d 0 2) (by simp) with h278 | h278
                                  · rcases p276_3 (m.d 1 2) (by simp) with h279 | h279
                                    · linarith only [h0, h279, hlam]
                                    · rcases p276_3 (m.d 2 3) (by simp) with h281 | h281
                                      · linarith only [h2, h281, hlam]
                                      · linarith only [h281, h7, hlam]
                                  · linarith only [h0, h278, hlam]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h0, h228, h230, h231, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p276_1]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h0, h230, h231, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p276_1]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  rcases p276_3 (m.d 0 2) (by simp) with h287 | h287
                                  · rcases p276_3 (m.d 1 2) (by simp) with h288 | h288
                                    · linarith only [h0, h288, hlam]
                                    · rcases p276_3 (m.d 2 3) (by simp) with h290 | h290
                                      · linarith only [h2, h290, hlam]
                                      · linarith only [h229, h290, hlam]
                                  · linarith only [h287, hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h0, hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h7, hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h74, hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h176, hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h2, hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p276_1, u3elo2]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h2, h230, h231, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p276_1, u3elo0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h176, h2, hc12, hlam, hphi, ht23, p276_1, u3elo0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h3, hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h3, h5, hc12, hlam, hphi, ht23, p276_1, u3elo0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h228, hlam, p276_1]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h176, h3, h5, hc12, hlam, hphi, ht23, p276_1, u3elo0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h4, hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h4, h6, hc12, hlam, hphi, ht23, p276_1, u3elo0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h229, hlam, p276_1]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [h230, hlam, p276_0]
                                · have p276_0 := h276c.1
                                  have p276_1 := h276c.2.1
                                  have p276_2 := h276c.2.2.1
                                  have p276_3 := h276c.2.2.2
                                  linarith only [hlam, p276_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h314 | h314
                              · linarith only [h230, h314, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                              · rcases h2bigk with h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c | h316c
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  rcases p316_3 (m.d 0 2) (by simp) with h318 | h318
                                  · rcases p316_3 (m.d 1 2) (by simp) with h319 | h319
                                    · linarith only [h0, h319, hlam]
                                    · rcases p316_3 (m.d 2 3) (by simp) with h321 | h321
                                      · linarith only [h2, h321, hlam]
                                      · linarith only [h321, h7, hlam]
                                  · linarith only [h0, h318, hlam]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  rcases p316_3 (m.d 0 2) (by simp) with h325 | h325
                                  · rcases p316_3 (m.d 1 2) (by simp) with h326 | h326
                                    · linarith only [h0, h326, hlam]
                                    · rcases p316_3 (m.d 2 3) (by simp) with h328 | h328
                                      · linarith only [h328, hlam, p316_0]
                                      · rcases p316_3 (m.d 2 4) (by simp) with h330 | h330
                                        · linarith only [h3, h330, hlam]
                                        · rcases p316_3 (m.d 2 5) (by simp) with h332 | h332
                                          · linarith only [h332, h4, hlam]
                                          · rcases h3bigk with h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c | h334c
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [hc13, hlam, hphi, p334_1, u3elo0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [hc23, hlam, hphi, p334_1, u3elo0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              rcases p334_3 (m.d 0 3) (by simp) with h338 | h338
                                              · rcases p334_3 (m.d 1 3) (by simp) with h339 | h339
                                                · linarith only [h1, h339, hlam]
                                                · linarith only [h227, h339, hlam]
                                              · linarith only [h338, hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              rcases p334_3 (m.d 0 3) (by simp) with h343 | h343
                                              · rcases p334_3 (m.d 1 3) (by simp) with h344 | h344
                                                · linarith only [h1, h344, hlam]
                                                · linarith only [h227, h344, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p334_1, u3elo0]
                                              · linarith only [h343, hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h1, hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h7, hlam, p334_1]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h0, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p316_1, p334_1]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h0, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p316_1, p334_1]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h2, hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p316_1, p334_1]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p316_1, p334_1]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h0, hc01, hc35, hlam, hphi, ht0b, ht5b, p316_1, p334_1]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h5, hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h227, hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h228, hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h314, hlam, p334_1]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h6, hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h0, h227, h229, h230, h74, hc01, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p316_1, p334_1, u3elo4]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h229, hlam, p334_0]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [h0, h229, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p316_1, p334_1]
                                            · have p334_0 := h334c.1
                                              have p334_1 := h334c.2.1
                                              have p334_2 := h334c.2.2.1
                                              have p334_3 := h334c.2.2.2
                                              linarith only [hlam, p334_0]
                                  · linarith only [h325, hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  rcases p316_3 (m.d 0 2) (by simp) with h369 | h369
                                  · rcases p316_3 (m.d 1 2) (by simp) with h370 | h370
                                    · linarith only [h0, h370, hlam]
                                    · rcases p316_3 (m.d 2 3) (by simp) with h372 | h372
                                      · linarith only [h2, h372, hlam]
                                      · linarith only [h228, h372, hlam]
                                  · linarith only [h369, hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  rcases p316_3 (m.d 0 2) (by simp) with h376 | h376
                                  · rcases p316_3 (m.d 1 2) (by simp) with h377 | h377
                                    · linarith only [h0, h377, hlam]
                                    · rcases p316_3 (m.d 2 3) (by simp) with h379 | h379
                                      · linarith only [h2, h379, hlam]
                                      · linarith only [h229, h379, hlam]
                                  · linarith only [h376, hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h0, hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h7, hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h74, hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h176, hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h2, hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p316_1, u3elo2]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h2, h74, hc12, hlam, hphi, ht23, p316_1, u3elo0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h176, h2, hc12, hlam, hphi, ht23, p316_1, u3elo0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h3, hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h3, h5, hc12, hlam, hphi, ht23, p316_1, u3elo0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h228, hlam, p316_1]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h230, hlam, p316_1]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h4, hlam, p316_0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h4, h6, hc12, hlam, hphi, ht23, p316_1, u3elo0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h229, hlam, p316_1]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [h4, h6, h74, hc12, hlam, hphi, ht23, p316_1, u3elo0]
                                · have p316_0 := h316c.1
                                  have p316_1 := h316c.2.1
                                  have p316_2 := h316c.2.2.1
                                  have p316_3 := h316c.2.2.2
                                  linarith only [hlam, p316_0]
                          · linarith only [h229, h6, hc23, hlam, hphi, u3elo0]
                        · linarith only [h228, h7, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h227, h5, hc13, hlam, hphi, u3elo0]
              · linarith only [h6, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h408 | h408
            · rcases m.htr 0 3 5 (by decide) (by decide) with h409 | h409
              · linarith only [h2, h4, h409, hlam]
              · linarith only [h409, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
            · linarith only [h408, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h413 | h413
          · rcases m.htr 0 3 4 (by decide) (by decide) with h414 | h414
            · linarith only [h2, h3, h414, hlam]
            · linarith only [h414, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h417 | h417
            · linarith only [h2, h3, h417, hlam]
            · linarith only [h417, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h422 | h422
    · rcases m.htr 0 2 3 (by decide) (by decide) with h423 | h423
      · rcases m.htr 0 2 4 (by decide) (by decide) with h424 | h424
        · rcases m.htr 0 2 5 (by decide) (by decide) with h425 | h425
          · rcases m.htr 0 3 4 (by decide) (by decide) with h426 | h426
            · rcases m.htr 0 3 5 (by decide) (by decide) with h427 | h427
              · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                · rcases m.htr 1 2 4 (by decide) (by decide) with h429 | h429
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h430 | h430
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h431 | h431
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h432 | h432
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h433 | h433
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h434 | h434
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h435 | h435
                              · linarith only [h0, h422, h428, h432, h435, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h0, h422, h429, h431, h434, h435, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h438 | h438
                              · linarith only [h426, h434, h438, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                              · rcases h2bigk with h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h0, hlam, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  rcases p440_3 (m.d 0 2) (by simp) with h443 | h443
                                  · rcases p440_3 (m.d 1 2) (by simp) with h444 | h444
                                    · rcases p440_3 (m.d 2 3) (by simp) with h445 | h445
                                      · linarith only [h445, hlam, p440_0]
                                      · rcases p440_3 (m.d 2 4) (by simp) with h447 | h447
                                        · linarith only [h424, h447, hlam]
                                        · rcases p440_3 (m.d 2 5) (by simp) with h449 | h449
                                          · linarith only [h425, h449, hlam]
                                          · rcases h3bigk with h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c | h451c
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [hc13, hlam, hphi, p451_1, u3elo0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h433, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p451_1, u3elo0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              rcases p451_3 (m.d 0 3) (by simp) with h455 | h455
                                              · rcases p451_3 (m.d 1 3) (by simp) with h456 | h456
                                                · linarith only [h422, h456, hlam]
                                                · linarith only [h431, h456, hlam]
                                              · linarith only [h455, hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              rcases p451_3 (m.d 0 3) (by simp) with h460 | h460
                                              · rcases p451_3 (m.d 1 3) (by simp) with h461 | h461
                                                · linarith only [h422, h461, hlam]
                                                · linarith only [h428, h433, h461, hlam]
                                              · linarith only [h460, hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h422, hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h433, h438, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p451_1, u3elo1]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h0, h422, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p451_1]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h0, h422, h438, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p451_1]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h423, hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h428, hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p440_1, p451_1]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h0, h438, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p440_1, p451_1]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h426, hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h431, hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h432, hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h438, hlam, p451_1]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h427, hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [hc13, hlam, hphi, p451_1, u3elo4]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h433, hlam, p451_0]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [h0, h433, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p440_1, p451_1]
                                            · have p451_0 := h451c.1
                                              have p451_1 := h451c.2.1
                                              have p451_2 := h451c.2.2.1
                                              have p451_3 := h451c.2.2.2
                                              linarith only [hlam, p451_0]
                                    · linarith only [h428, h444, hlam]
                                  · linarith only [h443, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  rcases p440_3 (m.d 0 2) (by simp) with h487 | h487
                                  · rcases p440_3 (m.d 1 2) (by simp) with h488 | h488
                                    · rcases p440_3 (m.d 2 3) (by simp) with h489 | h489
                                      · linarith only [h423, h489, hlam]
                                      · linarith only [h432, h489, hlam]
                                    · linarith only [h429, h488, hlam]
                                  · linarith only [h487, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  rcases p440_3 (m.d 0 2) (by simp) with h494 | h494
                                  · rcases p440_3 (m.d 1 2) (by simp) with h495 | h495
                                    · rcases p440_3 (m.d 2 3) (by simp) with h496 | h496
                                      · linarith only [h423, h496, hlam]
                                      · linarith only [h433, h496, hlam]
                                    · linarith only [h430, h495, hlam]
                                  · linarith only [h494, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht01, p440_1, u0ehi1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  rcases p440_3 (m.d 0 2) (by simp) with h503 | h503
                                  · linarith only [h0, h503, hlam]
                                  · linarith only [h423, h503, hlam]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  rcases p440_3 (m.d 0 2) (by simp) with h506 | h506
                                  · linarith only [h0, h506, hlam]
                                  · linarith only [h424, h506, hlam]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  rcases p440_3 (m.d 0 2) (by simp) with h509 | h509
                                  · linarith only [h0, h509, hlam]
                                  · linarith only [h425, h509, hlam]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h423, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h428, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h0, h422, h428, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h0, h422, h428, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h424, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h429, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h432, hlam, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h434, hlam, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h425, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h430, hlam, p440_0]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h433, hlam, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [h0, h422, h428, h432, h433, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p440_1]
                                · have p440_0 := h440c.1
                                  have p440_1 := h440c.2.1
                                  have p440_2 := h440c.2.2.1
                                  have p440_3 := h440c.2.2.2
                                  linarith only [hlam, p440_0]
                          · linarith only [h427, h433, hc23, hlam, hphi, u3elo0]
                        · linarith only [h426, h432, hc23, hlam, hphi, u3elo0]
                      · linarith only [h426, h431, hc13, hlam, hphi, u3elo0]
                    · linarith only [h0, h425, h430, hc02, hlam, hphi, u0ehi0]
                  · linarith only [h0, h429, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h422, h427, h428, hc23, hlam, hphi, ht01, ht12, u0ehi4]
              · linarith only [h427, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
            · linarith only [h426, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h535 | h535
            · rcases m.htr 0 3 5 (by decide) (by decide) with h536 | h536
              · linarith only [h0, h422, h425, h536, hlam]
              · linarith only [h536, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo4]
            · linarith only [h535, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h540 | h540
          · rcases m.htr 0 3 4 (by decide) (by decide) with h541 | h541
            · linarith only [h0, h422, h424, h541, hlam]
            · linarith only [h541, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h544 | h544
            · linarith only [h0, h422, h424, h544, hlam]
            · linarith only [h544, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · linarith only [h0, h422, h423, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo2]
    · linarith only [h422, hlam, hphi, ht01, ht12, ht23, u0ehi0, u3elo1]

end R2N4
