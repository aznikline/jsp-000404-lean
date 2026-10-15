import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_I_L_0_L_I_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2elo := hb2.1
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h14, h16, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h16, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h15, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                                · linarith only [h14, h20, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                · linarith only [h20, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h12, h13, h8, hc34, hlam, hphi, ht45, u5elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                            · linarith only [h12, h24, h4, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · linarith only [h24, hc13, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h11, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h10, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h4, h9, hc12, hlam, hphi, u2elo0]
                  · linarith only [h8, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h31 | h31
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                          · linarith only [h1, h31, h35, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                              · linarith only [h0, h1, h32, h37, h38, h7, hc02, hc35, hlam, hphi, ht0b, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                                  · rcases h0bigk with h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [hlam, p42_0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h4, h40, h41, hc01, hc45, hlam, hphi, ht0b, ht5b, p42_1]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      rcases p42_3 (m.d 0 1) (by simp) with h45 | h45
                                      · rcases p42_3 (m.d 0 2) (by simp) with h46 | h46
                                        · linarith only [h0, h46, hlam]
                                        · linarith only [h4, h46, hlam]
                                      · linarith only [h1, h45, hlam]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      rcases p42_3 (m.d 0 1) (by simp) with h50 | h50
                                      · rcases p42_3 (m.d 0 2) (by simp) with h51 | h51
                                        · linarith only [h0, h51, hlam]
                                        · linarith only [h5, h51, hlam]
                                      · linarith only [h2, h50, hlam]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      rcases p42_3 (m.d 0 1) (by simp) with h55 | h55
                                      · rcases p42_3 (m.d 0 2) (by simp) with h56 | h56
                                        · linarith only [h0, h56, hlam]
                                        · linarith only [h56, h6, hlam]
                                      · linarith only [h3, h55, hlam]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h0, hlam, p42_0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [hlam, p42_0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h1, h32, h40, h41, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p42_1, u2elo0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h1, h32, h40, h41, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p42_1, u2elo0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      rcases p42_3 (m.d 0 1) (by simp) with h64 | h64
                                      · rcases p42_3 (m.d 0 2) (by simp) with h65 | h65
                                        · rcases p42_3 (m.d 0 3) (by simp) with h66 | h66
                                          · linarith only [h4, h66, hlam]
                                          · linarith only [h31, h66, hlam]
                                        · linarith only [h6, h65, hlam]
                                      · linarith only [h3, h64, hlam]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h1, hlam, p42_1]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h4, hlam, p42_1]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [hlam, p42_0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h7, hlam, p42_1]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      rcases p42_3 (m.d 0 1) (by simp) with h75 | h75
                                      · rcases p42_3 (m.d 0 2) (by simp) with h76 | h76
                                        · rcases p42_3 (m.d 0 3) (by simp) with h77 | h77
                                          · rcases p42_3 (m.d 0 4) (by simp) with h78 | h78
                                            · rcases p42_3 (m.d 0 5) (by simp) with h79 | h79
                                              · linarith only [h31, h79, hlam]
                                              · rcases h0emin with h81 | h81 | h81 | h81 | h81
                                                · rcases h3bigk with h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h32, h40, h41, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p82_1]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h40, h41, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p82_1]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h7, hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    rcases p82_3 (m.d 0 3) (by simp) with h87 | h87
                                                    · rcases p82_3 (m.d 1 3) (by simp) with h88 | h88
                                                      · linarith only [h1, h88, hlam]
                                                      · linarith only [h37, h88, hlam]
                                                    · linarith only [h87, hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h1, hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h1, h40, h41, hc01, hc45, hlam, hphi, ht0b, ht5b, p82_1]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h35, hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    rcases p82_3 (m.d 0 3) (by simp) with h96 | h96
                                                    · rcases p82_3 (m.d 1 3) (by simp) with h97 | h97
                                                      · rcases p82_3 (m.d 2 3) (by simp) with h98 | h98
                                                        · linarith only [h32, h98, hlam]
                                                        · linarith only [h40, h98, hlam]
                                                      · linarith only [h97, hlam, p82_0]
                                                    · linarith only [h31, h96, hlam]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h4, hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h32, hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h38, hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h4, h41, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p82_1, u2elo0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h3, h34, h40, h41, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p42_1, p82_1]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    rcases p82_3 (m.d 0 3) (by simp) with h109 | h109
                                                    · linarith only [h109, h7, hlam]
                                                    · linarith only [h1, h109, hlam]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    rcases p82_3 (m.d 0 3) (by simp) with h112 | h112
                                                    · linarith only [h112, h7, hlam]
                                                    · linarith only [h112, h4, hlam]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h3, h34, h40, h7, hlam, p42_1, p82_2]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h31, hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h37, hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h40, hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [h41, hlam, p82_0]
                                                  · have p82_0 := h82c.1
                                                    have p82_1 := h82c.2.1
                                                    have p82_2 := h82c.2.2.1
                                                    have p82_3 := h82c.2.2.2
                                                    linarith only [hlam, p82_0]
                                                · linarith only [h81, hlam, ht01, ht12, u2elo0]
                                                · linarith only [h4, h81, hlam, ht01, ht12, u2elo0]
                                                · linarith only [h5, h81, hlam, ht01, ht12, u2elo0]
                                                · linarith only [h81, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                            · linarith only [h7, h78, hlam, p42_1]
                                          · linarith only [h31, h77, hlam]
                                        · linarith only [h6, h76, hlam]
                                      · linarith only [h3, h75, hlam]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h2, hlam, p42_0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h5, hlam, p42_0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h4, h40, h41, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p42_1, u2elo0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [hlam, p42_0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      rcases p42_3 (m.d 0 1) (by simp) with h134 | h134
                                      · rcases p42_3 (m.d 0 2) (by simp) with h135 | h135
                                        · rcases p42_3 (m.d 0 3) (by simp) with h136 | h136
                                          · linarith only [h136, h7, hlam]
                                          · linarith only [h136, h31, hlam]
                                        · linarith only [h135, h6, hlam]
                                      · linarith only [h134, h3, hlam]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h3, hlam, p42_0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h6, hlam, p42_1]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [h31, hlam, p42_0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [hc04, hlam, hphi, ht45, p42_1, u5elo0]
                                    · have p42_0 := h42c.1
                                      have p42_1 := h42c.2.1
                                      have p42_2 := h42c.2.2.1
                                      have p42_3 := h42c.2.2.2
                                      linarith only [hlam, p42_0]
                                  · linarith only [h41, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h1, h37, h40, h7, hc23, hc34, hlam, hphi]
                            · linarith only [h31, h37, hc13, hlam, hphi, ht34, ht45, u5elo0]
                        · linarith only [h32, h34, hc23, hlam, hphi, ht34, ht45, u5elo2]
                      · linarith only [h32, h33, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h32, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h31, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h6, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h154 | h154
              · rcases m.htr 0 3 4 (by decide) (by decide) with h155 | h155
                · linarith only [h155, h4, h5, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h157 | h157
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
                      · linarith only [h0, h159, h5, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                          · linarith only [h1, h155, h157, h162, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h164 | h164
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                              · linarith only [h0, h1, h155, h158, h164, h165, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h167 | h167
                                · linarith only [h0, h158, h167, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                                · linarith only [h167, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h157, h164, h4, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · linarith only [h161, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h158, h4, h5, hc12, hlam, hphi, u2elo3]
                  · linarith only [h157, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h154, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h175 | h175
            · rcases m.htr 0 2 5 (by decide) (by decide) with h176 | h176
              · rcases m.htr 0 3 4 (by decide) (by decide) with h177 | h177
                · rcases m.htr 0 3 5 (by decide) (by decide) with h178 | h178
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                    · linarith only [h175, h179, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h183 | h183
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h186 | h186
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                                  · linarith only [h0, h181, h185, h187, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                                  · linarith only [h187, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h186, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                              · linarith only [h0, h177, h181, h185, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h179, h181, h184, hc24, hlam, hphi, ht45, u5elo3]
                          · linarith only [h177, h179, h181, h183, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · linarith only [h181, h182, hc24, hlam, hphi, ht45, u5elo2]
                      · linarith only [h175, h181, h4, hc12, hlam, hphi, u2elo2]
                  · linarith only [h178, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h175, h177, h4, hlam]
              · linarith only [h176, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h199 | h199
              · rcases m.htr 0 3 4 (by decide) (by decide) with h200 | h200
                · rcases m.htr 0 3 5 (by decide) (by decide) with h201 | h201
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
                    · linarith only [h0, h202, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h204 | h204
                      · linarith only [h0, h175, h204, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h206 | h206
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h207 | h207
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h208 | h208
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h209 | h209
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h210 | h210
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h211 | h211
                                  · rcases h0bigk with h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      rcases p212_3 (m.d 0 1) (by simp) with h214 | h214
                                      · rcases p212_3 (m.d 0 2) (by simp) with h215 | h215
                                        · linarith only [h0, h215, hlam]
                                        · rcases p212_3 (m.d 0 3) (by simp) with h217 | h217
                                          · linarith only [h1, h217, hlam]
                                          · linarith only [h217, h4, hlam]
                                      · linarith only [h0, h214, hlam]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h1, h207, h211, hc01, hc45, hlam, hphi, ht0b, ht5b, p212_1]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      rcases p212_3 (m.d 0 1) (by simp) with h222 | h222
                                      · rcases p212_3 (m.d 0 2) (by simp) with h223 | h223
                                        · linarith only [h0, h223, hlam]
                                        · rcases p212_3 (m.d 0 3) (by simp) with h225 | h225
                                          · linarith only [h1, h225, hlam]
                                          · linarith only [h200, h225, hlam]
                                      · linarith only [h2, h222, hlam]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      rcases p212_3 (m.d 0 1) (by simp) with h229 | h229
                                      · rcases p212_3 (m.d 0 2) (by simp) with h230 | h230
                                        · linarith only [h0, h230, hlam]
                                        · linarith only [h199, h230, hlam]
                                      · linarith only [h229, h3, hlam]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h0, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h4, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h175, hlam, p212_1]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h175, h209, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p212_1, u2elo2]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h1, hlam, p212_1]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h4, hc02, hlam, hphi, p212_1, u2elo2]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h2, h204, h4, hc12, hlam, hphi, p212_1, u2elo2]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      rcases p212_3 (m.d 0 1) (by simp) with h243 | h243
                                      · rcases p212_3 (m.d 0 2) (by simp) with h244 | h244
                                        · linarith only [h244, h4, hlam]
                                        · linarith only [h199, h244, hlam]
                                      · linarith only [h243, h3, hlam]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h2, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h0, h175, h206, h209, h210, h211, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p212_1, u2elo2]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h200, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      rcases p212_3 (m.d 0 1) (by simp) with h252 | h252
                                      · rcases p212_3 (m.d 0 2) (by simp) with h253 | h253
                                        · linarith only [h175, h253, hlam]
                                        · linarith only [h199, h253, hlam]
                                      · linarith only [h252, h3, hlam]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h3, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h199, hlam, p212_1]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [h201, hlam, p212_0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [hc04, hlam, hphi, ht45, p212_1, u5elo0]
                                    · have p212_0 := h212c.1
                                      have p212_1 := h212c.2.1
                                      have p212_2 := h212c.2.2.1
                                      have p212_3 := h212c.2.2.2
                                      linarith only [hlam, p212_0]
                                  · linarith only [h211, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h210, h4, hc03, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h0, h200, h206, h209, h4, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h204, h206, h207, h208, hc25, hlam, hphi, u5elo3]
                          · linarith only [h200, h202, h206, h207, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · linarith only [h206, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h201, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h269 | h269
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h270 | h270
                    · linarith only [h0, h270, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h272 | h272
                      · linarith only [h0, h175, h272, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h274 | h274
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h275 | h275
                          · linarith only [h1, h200, h269, h275, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h277 | h277
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h278 | h278
                              · linarith only [h0, h200, h274, h278, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h280 | h280
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h281 | h281
                                  · rcases h0bigk with h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [hlam, p282_0]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      rcases p282_3 (m.d 0 1) (by simp) with h284 | h284
                                      · rcases p282_3 (m.d 0 2) (by simp) with h285 | h285
                                        · linarith only [h0, h285, hlam]
                                        · rcases p282_3 (m.d 0 3) (by simp) with h287 | h287
                                          · linarith only [h1, h287, hlam]
                                          · linarith only [h287, h4, hlam]
                                      · linarith only [h0, h284, hlam]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      rcases p282_3 (m.d 0 1) (by simp) with h291 | h291
                                      · rcases p282_3 (m.d 0 2) (by simp) with h292 | h292
                                        · linarith only [h0, h292, hlam]
                                        · rcases p282_3 (m.d 0 3) (by simp) with h294 | h294
                                          · linarith only [h1, h294, hlam]
                                          · rcases p282_3 (m.d 0 4) (by simp) with h296 | h296
                                            · linarith only [h2, h296, hlam]
                                            · linarith only [h200, h296, hlam]
                                      · linarith only [h1, h291, hlam]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      rcases p282_3 (m.d 0 1) (by simp) with h300 | h300
                                      · rcases p282_3 (m.d 0 2) (by simp) with h301 | h301
                                        · linarith only [h0, h301, hlam]
                                        · rcases p282_3 (m.d 0 3) (by simp) with h303 | h303
                                          · linarith only [h1, h303, hlam]
                                          · rcases p282_3 (m.d 0 4) (by simp) with h305 | h305
                                            · linarith only [h2, h305, hlam]
                                            · rcases p282_3 (m.d 0 5) (by simp) with h307 | h307
                                              · linarith only [h3, h307, hlam]
                                              · rcases h0emin with h309 | h309 | h309 | h309 | h309
                                                · rcases h3bigk with h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [hlam, p310_0]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h278, h4, hc13, hc34, hlam, hphi, p310_1]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h4, hlam, p310_1]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h200, hlam, p310_0]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h200, h281, hc01, hc45, hlam, hphi, ht0b, ht5b, p282_1, p310_1]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h1, hlam, p310_0]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [hlam, p310_0]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h270, hlam, p310_1]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h275, hlam, p310_0]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h1, h200, h281, hc01, hc45, hlam, hphi, ht0b, ht5b, p282_1, p310_1]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h278, hc03, hc34, hlam, hphi, p310_1]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h278, hc13, hc34, hlam, hphi, p310_1]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [hlam, p310_0]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h278, hlam, p310_0]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    rcases p310_3 (m.d 0 3) (by simp) with h325 | h325
                                                    · linarith only [h325, h4, hlam]
                                                    · linarith only [h269, h325, hlam]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    rcases p310_3 (m.d 0 3) (by simp) with h328 | h328
                                                    · linarith only [h328, hlam, p310_0]
                                                    · rcases p310_3 (m.d 1 3) (by simp) with h330 | h330
                                                      · linarith only [h275, h330, hlam]
                                                      · rcases p310_3 (m.d 2 3) (by simp) with h332 | h332
                                                        · linarith only [h278, h332, hlam]
                                                        · linarith only [h332, h4, hlam]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    rcases p310_3 (m.d 0 3) (by simp) with h335 | h335
                                                    · linarith only [h200, h335, hlam]
                                                    · linarith only [h1, h335, hlam]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h0, h274, h280, h281, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p310_1]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [hlam, p310_0]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h0, h274, h278, h280, h4, hlam, p310_2]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h269, hlam, p310_0]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h277, hlam, p310_0]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h280, hlam, p310_0]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [h281, hlam, p310_0]
                                                  · have p310_0 := h310c.1
                                                    have p310_1 := h310c.2.1
                                                    have p310_2 := h310c.2.2.1
                                                    have p310_3 := h310c.2.2.2
                                                    linarith only [hlam, p310_0]
                                                · linarith only [h309, h4, hlam, ht01, ht12, u2elo2]
                                                · linarith only [h309, h4, hlam, ht01, ht12, u2elo2]
                                                · linarith only [h309, hc01, hlam, p282_1]
                                                · linarith only [h309, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                      · linarith only [h2, h300, hlam]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      rcases p282_3 (m.d 0 1) (by simp) with h351 | h351
                                      · rcases p282_3 (m.d 0 2) (by simp) with h352 | h352
                                        · linarith only [h0, h352, hlam]
                                        · linarith only [h199, h352, hlam]
                                      · linarith only [h3, h351, hlam]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h0, hlam, p282_0]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [hlam, p282_0]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h4, hlam, p282_0]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h175, hlam, p282_1]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h278, h4, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p282_1]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h1, hlam, p282_1]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h175, h200, hc02, hlam, hphi, p282_1, u2elo3]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [hlam, p282_0]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h200, hlam, p282_1]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      rcases p282_3 (m.d 0 1) (by simp) with h365 | h365
                                      · rcases p282_3 (m.d 0 2) (by simp) with h366 | h366
                                        · linarith only [h366, h4, hlam]
                                        · linarith only [h199, h366, hlam]
                                      · linarith only [h3, h365, hlam]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h2, hlam, p282_0]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h0, h175, h274, h280, h281, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p282_1, u2elo3]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h1, h175, h270, h274, h280, h281, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p282_1, u2elo3]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [hlam, p282_0]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      rcases p282_3 (m.d 0 1) (by simp) with h374 | h374
                                      · rcases p282_3 (m.d 0 2) (by simp) with h375 | h375
                                        · linarith only [h175, h375, hlam]
                                        · linarith only [h199, h375, hlam]
                                      · linarith only [h3, h374, hlam]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h3, hlam, p282_0]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h199, hlam, p282_1]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [h269, hlam, p282_0]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [hc04, hlam, hphi, ht45, p282_1, u5elo0]
                                    · have p282_0 := h282c.1
                                      have p282_1 := h282c.2.1
                                      have p282_2 := h282c.2.2.1
                                      have p282_3 := h282c.2.2.2
                                      linarith only [hlam, p282_0]
                                  · linarith only [h278, h281, hc23, hlam, hphi, ht34, ht45, u5elo4]
                                · linarith only [h280, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                            · linarith only [h200, h269, h270, h274, h277, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h274, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                  · linarith only [h269, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h199, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h391 | h391
        · rcases m.htr 0 2 3 (by decide) (by decide) with h392 | h392
          · rcases m.htr 0 2 4 (by decide) (by decide) with h393 | h393
            · linarith only [h0, h2, h393, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h395 | h395
              · rcases m.htr 0 3 4 (by decide) (by decide) with h396 | h396
                · linarith only [h1, h2, h396, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h398 | h398
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h399 | h399
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h400 | h400
                      · linarith only [h0, h2, h393, h400, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h0, h2, h399, h400, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h2, h392, h393, h399, hc12, hlam, hphi, u2elo3]
                  · linarith only [h398, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h395, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h406 | h406
            · linarith only [h0, h2, h392, h406, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h408 | h408
              · rcases m.htr 0 3 4 (by decide) (by decide) with h409 | h409
                · linarith only [h1, h2, h409, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h411 | h411
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h412 | h412
                    · linarith only [h0, h2, h392, h412, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h414 | h414
                      · linarith only [h0, h2, h406, h414, hlam]
                      · linarith only [h1, h2, h412, h414, hc12, hlam, hphi, u2elo3]
                  · linarith only [h411, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h408, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h391, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h420 | h420
      · rcases m.htr 0 1 5 (by decide) (by decide) with h421 | h421
        · rcases m.htr 0 2 3 (by decide) (by decide) with h422 | h422
          · linarith only [h0, h1, h422, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h424 | h424
            · rcases m.htr 0 2 5 (by decide) (by decide) with h425 | h425
              · rcases m.htr 0 3 4 (by decide) (by decide) with h426 | h426
                · rcases m.htr 0 3 5 (by decide) (by decide) with h427 | h427
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                    · linarith only [h0, h1, h422, h428, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1, h428, hc12, hlam, hphi, u2elo2]
                  · linarith only [h427, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h1, h424, h426, hlam]
              · linarith only [h425, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h434 | h434
              · rcases m.htr 0 3 4 (by decide) (by decide) with h435 | h435
                · rcases m.htr 0 3 5 (by decide) (by decide) with h436 | h436
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
                    · linarith only [h0, h422, h437, hlam]
                    · linarith only [h0, h1, h437, hc12, hlam, hphi, u2elo2]
                  · linarith only [h0, h1, h436, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h1, h420, h435, hlam]
              · linarith only [h434, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h421, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h444 | h444
        · rcases m.htr 0 2 3 (by decide) (by decide) with h445 | h445
          · linarith only [h0, h1, h445, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h447 | h447
            · linarith only [h0, h420, h447, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h449 | h449
              · rcases m.htr 0 3 4 (by decide) (by decide) with h450 | h450
                · rcases m.htr 0 3 5 (by decide) (by decide) with h451 | h451
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h452 | h452
                    · linarith only [h0, h1, h445, h452, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1, h452, hc12, hlam, hphi, u2elo2]
                  · linarith only [h451, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h456 | h456
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h457 | h457
                    · linarith only [h0, h1, h450, h457, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1, h457, hc12, hlam, hphi, u2elo2]
                  · linarith only [h456, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h449, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h444, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h463 | h463
    · rcases m.htr 0 1 4 (by decide) (by decide) with h464 | h464
      · rcases m.htr 0 1 5 (by decide) (by decide) with h465 | h465
        · rcases m.htr 0 2 3 (by decide) (by decide) with h466 | h466
          · rcases m.htr 0 2 4 (by decide) (by decide) with h467 | h467
            · rcases m.htr 0 2 5 (by decide) (by decide) with h468 | h468
              · rcases m.htr 0 3 4 (by decide) (by decide) with h469 | h469
                · rcases m.htr 0 3 5 (by decide) (by decide) with h470 | h470
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h472 | h472
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h473 | h473
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h474 | h474
                          · linarith only [h0, h463, h474, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h0, h463, h469, h471, h474, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h473, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h472, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h471, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h469, h470, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h481 | h481
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h482 | h482
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h483 | h483
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h484 | h484
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h485 | h485
                          · linarith only [h0, h463, h469, h485, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h487 | h487
                            · linarith only [h0, h464, h485, h487, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h469, h481, h482, h487, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h484, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h483, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h463, h482, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · linarith only [h481, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h468, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h464, h467, hlam]
          · linarith only [h0, h463, h466, hlam]
        · linarith only [h463, h465, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h498 | h498
        · rcases m.htr 0 2 3 (by decide) (by decide) with h499 | h499
          · rcases m.htr 0 2 4 (by decide) (by decide) with h500 | h500
            · rcases m.htr 0 2 5 (by decide) (by decide) with h501 | h501
              · rcases m.htr 0 3 4 (by decide) (by decide) with h502 | h502
                · linarith only [h463, h464, h502, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h504 | h504
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h505 | h505
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h506 | h506
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h507 | h507
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h508 | h508
                          · linarith only [h463, h464, h502, h506, h508, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h510 | h510
                            · linarith only [h463, h464, h506, h510, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h505, h510, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h464, h506, h507, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h500, h506, hlam]
                    · linarith only [h0, h505, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h504, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h501, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h518 | h518
              · rcases m.htr 0 3 4 (by decide) (by decide) with h519 | h519
                · linarith only [h0, h463, h500, h519, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h521 | h521
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h522 | h522
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h523 | h523
                      · linarith only [h0, h463, h500, h522, h523, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h463, h522, h523, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h522, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h521, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h463, h518, hc13, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h0, h463, h499, hlam]
        · linarith only [h463, h498, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h531 | h531
      · rcases m.htr 0 1 5 (by decide) (by decide) with h532 | h532
        · rcases m.htr 0 2 3 (by decide) (by decide) with h533 | h533
          · rcases m.htr 0 2 4 (by decide) (by decide) with h534 | h534
            · rcases m.htr 0 2 5 (by decide) (by decide) with h535 | h535
              · rcases m.htr 0 3 4 (by decide) (by decide) with h536 | h536
                · rcases m.htr 0 3 5 (by decide) (by decide) with h537 | h537
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h538 | h538
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h539 | h539
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h540 | h540
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h541 | h541
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h542 | h542
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h543 | h543
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h544 | h544
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h545 | h545
                                  · linarith only [h533, h543, h545, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h545, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h544, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · linarith only [h463, h531, h538, h541, h543, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h463, h542, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                          · linarith only [h463, h531, h536, h539, h541, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h463, h531, h538, h539, h540, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h463, h531, h538, h539, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h531, h538, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h537, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h463, h531, h536, hlam]
              · linarith only [h535, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h463, h531, h533, h534, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h559 | h559
            · rcases m.htr 0 2 5 (by decide) (by decide) with h560 | h560
              · rcases m.htr 0 3 4 (by decide) (by decide) with h561 | h561
                · rcases m.htr 0 3 5 (by decide) (by decide) with h562 | h562
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h563 | h563
                    · linarith only [h533, h563, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h531, h563, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h0, h531, h533, h562, hc14, hlam, hphi, ht45, u5elo3]
                · linarith only [h0, h531, h533, h561, hlam]
              · linarith only [h0, h531, h560, hc14, hlam, hphi, ht45, u5elo2]
            · linarith only [h0, h531, h559, hlam]
        · linarith only [h531, h532, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h571 | h571
        · rcases m.htr 0 2 3 (by decide) (by decide) with h572 | h572
          · rcases m.htr 0 2 4 (by decide) (by decide) with h573 | h573
            · rcases m.htr 0 2 5 (by decide) (by decide) with h574 | h574
              · rcases m.htr 0 3 4 (by decide) (by decide) with h575 | h575
                · rcases m.htr 0 3 5 (by decide) (by decide) with h576 | h576
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h577 | h577
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h578 | h578
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h579 | h579
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h580 | h580
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h581 | h581
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h582 | h582
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h583 | h583
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h584 | h584
                                  · linarith only [h572, h582, h584, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h584, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h583, hc23, hlam, hphi, ht34, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h588 | h588
                                · linarith only [h463, h575, h577, h582, h588, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                · linarith only [h588, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h531, h571, h576, h579, h580, h581, hc25, hlam, hphi, u5elo0]
                          · linarith only [h463, h575, h580, hlam]
                        · linarith only [h0, h579, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h463, h571, h577, h578, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h0, h571, h577, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h576, hc03, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h597 | h597
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h598 | h598
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h599 | h599
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h600 | h600
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h601 | h601
                          · linarith only [h463, h571, h575, h598, h600, h601, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h603 | h603
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h604 | h604
                              · linarith only [h572, h601, h604, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h606 | h606
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h607 | h607
                                  · rcases h0bigk with h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [hlam, p608_0]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h0, hlam, p608_1]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h463, hlam, p608_0]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h531, hlam, p608_1]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h463, h601, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p608_1]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p608_1, u2elo1]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [hlam, p608_0]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h0, h463, h571, h600, h606, h607, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p608_1, u2elo1]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h0, h463, h571, h575, h600, h606, h607, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p608_1, u2elo1]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      rcases p608_3 (m.d 0 1) (by simp) with h618 | h618
                                      · linarith only [h0, h618, hlam]
                                      · linarith only [h571, h618, hlam]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h463, h571, h599, h600, h601, h606, h607, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p608_1, u2elo1]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h572, hlam, p608_1]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [hlam, p608_0]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h575, hlam, p608_1]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      rcases p608_3 (m.d 0 1) (by simp) with h625 | h625
                                      · linarith only [h463, h625, hlam]
                                      · linarith only [h571, h625, hlam]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h531, h571, h599, h600, h606, h607, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p608_1, u2elo1]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h573, hlam, p608_0]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h463, h531, h571, h599, h600, h606, h607, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p608_1, u2elo1]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [hlam, p608_0]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      rcases p608_3 (m.d 0 1) (by simp) with h632 | h632
                                      · linarith only [h531, h632, hlam]
                                      · linarith only [h571, h632, hlam]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h571, hlam, p608_0]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h574, hlam, p608_1]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [h597, hlam, p608_0]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [hc04, hlam, hphi, ht45, p608_1, u5elo0]
                                    · have p608_0 := h608c.1
                                      have p608_1 := h608c.2.1
                                      have p608_2 := h608c.2.2.1
                                      have p608_3 := h608c.2.2.2
                                      linarith only [hlam, p608_0]
                                  · linarith only [h607, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h606, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h463, h571, h575, h597, h603, hc04, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h600, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                      · linarith only [h463, h571, h598, h599, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h0, h571, h598, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h463, h571, h597, hc15, hlam, hphi, u5elo3]
              · linarith only [h574, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h648 | h648
              · rcases m.htr 0 3 4 (by decide) (by decide) with h649 | h649
                · linarith only [h572, h573, h649, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h651 | h651
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h652 | h652
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h653 | h653
                      · linarith only [h572, h573, h653, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h571, h653, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h0, h571, h572, h652, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h651, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h648, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h659 | h659
            · rcases m.htr 0 2 5 (by decide) (by decide) with h660 | h660
              · rcases m.htr 0 3 4 (by decide) (by decide) with h661 | h661
                · rcases m.htr 0 3 5 (by decide) (by decide) with h662 | h662
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h663 | h663
                    · linarith only [h531, h571, h572, h659, h663, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h571, h663, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h531, h571, h572, h659, h662, hc15, hlam, hphi, u5elo3]
                · linarith only [h572, h659, h661, hlam]
              · linarith only [h531, h571, h659, h660, hc15, hlam, hphi, u5elo2]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h669 | h669
              · rcases m.htr 0 3 4 (by decide) (by decide) with h670 | h670
                · rcases m.htr 0 3 5 (by decide) (by decide) with h671 | h671
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h672 | h672
                    · linarith only [h572, h672, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h571, h672, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h0, h571, h659, h670, h671, hc15, hlam, hphi, u5elo3]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h676 | h676
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h677 | h677
                    · linarith only [h0, h571, h572, h677, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h571, h677, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h676, hc03, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h0, h571, h669, hc15, hlam, hphi, u5elo2]
        · linarith only [h571, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

end R2N4
