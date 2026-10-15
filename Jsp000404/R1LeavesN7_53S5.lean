import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4696000 in
set_option maxHeartbeats 4696000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                      · linarith only [h0, h10, h12, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h10, h14, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
                          · linarith only [h0, h10, h16, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h0, h16, h4, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
                    · linarith only [h0, h19, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                      · linarith only [h0, h19, h21, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
                        · linarith only [h0, h19, h23, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
                          · linarith only [h1, h25, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h0, h25, h4, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h29 | h29
                · linarith only [h29, h7, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
                    · linarith only [h0, h32, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
                      · linarith only [h0, h32, h34, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                        · linarith only [h0, h32, h36, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h38 | h38
                          · linarith only [h1, h38, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h40 | h40
                            · linarith only [h29, h32, h4, h40, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                                · linarith only [h4, h43, h7, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                                  · linarith only [h29, h4, h45, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                                    · rcases h0bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [hlam, p48_0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h6, hc25, hlam, hphi, ht0b, ht5b, p48_1, u0elo0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h32, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u0elo0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h2, h42, hc45, hlam, hphi, ht0b, ht5b, p48_1, u0elo0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h29, h32, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u0elo0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h0, hlam, p48_0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [hlam, p48_0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h32, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u0elo1]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h0, h32, h4, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u0elo0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h0, h29, h32, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u0elo0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h1, hlam, p48_1]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h4, hlam, p48_1]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [hlam, p48_0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h7, hlam, p48_1]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h29, hlam, p48_1]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h2, hlam, p48_0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h5, hlam, p48_0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h32, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u0elo3]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [hlam, p48_0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h29, h32, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u0elo3]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h3, hlam, p48_0]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h6, hlam, p48_1]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h32, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p48_1, u0elo4]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [h31, hlam, p48_1]
                                      · have p48_0 := h48c.1
                                        have p48_1 := h48c.2.1
                                        have p48_2 := h48c.2.2.1
                                        have p48_3 := h48c.2.2.2
                                        linarith only [hlam, p48_0]
                                    · linarith only [h32, h4, h47, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h31, h38, h42, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
                    · linarith only [h0, h76, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
                      · linarith only [h0, h4, h76, h78, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h80 | h80
                        · linarith only [h0, h4, h76, h80, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                          · linarith only [h1, h7, h82, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
                            · linarith only [h1, h84, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                              · linarith only [h0, h31, h5, h78, h86, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h88 | h88
                                · linarith only [h4, h7, h88, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                                  · linarith only [h29, h4, h90, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h92 | h92
                                    · linarith only [h31, h4, h7, h76, h92, hc12, hc34, hlam, hphi, ht23]
                                    · linarith only [h4, h7, h76, h92, hc12, hc45, hlam, hphi, ht23, ht34]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h95 | h95
              · rcases m.htr 0 3 5 (by decide) (by decide) with h96 | h96
                · linarith only [h4, h6, h96, hlam]
                · linarith only [h95, h96, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h99 | h99
                · linarith only [h95, h99, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h101 | h101
                  · linarith only [h101, h5, h6, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
                    · linarith only [h0, h103, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h103, h4, h6, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h106 | h106
            · rcases m.htr 0 3 4 (by decide) (by decide) with h107 | h107
              · linarith only [h107, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h109 | h109
                · linarith only [h107, h109, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h111 | h111
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
                    · linarith only [h0, h112, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h112, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h111, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h116 | h116
              · linarith only [h116, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h118 | h118
                · linarith only [h116, h118, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h120 | h120
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
                    · linarith only [h0, h121, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h121, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h120, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h125 | h125
          · rcases m.htr 0 2 5 (by decide) (by decide) with h126 | h126
            · rcases m.htr 0 3 4 (by decide) (by decide) with h127 | h127
              · rcases m.htr 0 3 5 (by decide) (by decide) with h128 | h128
                · rcases m.htr 0 4 5 (by decide) (by decide) with h129 | h129
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h130 | h130
                    · linarith only [h0, h130, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h133 | h133
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                          · linarith only [h1, h134, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h127, h134, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h126, h133, h4, hc12, hc23, hlam, hphi]
                      · linarith only [h125, h132, h4, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h139 | h139
                    · linarith only [h0, h139, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h141 | h141
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                          · linarith only [h1, h143, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h127, h143, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h126, h142, h4, hc12, hc23, hlam, hphi]
                      · linarith only [h125, h141, h4, hc12, hc23, hlam, hphi]
                · linarith only [h127, h128, hc35, hlam, hphi, u3ehi3]
              · linarith only [h125, h127, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h150 | h150
              · rcases m.htr 0 3 5 (by decide) (by decide) with h151 | h151
                · rcases m.htr 0 4 5 (by decide) (by decide) with h152 | h152
                  · linarith only [h125, h126, h152, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
                    · linarith only [h0, h154, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h156 | h156
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h157 | h157
                        · linarith only [h0, h126, h157, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h159 | h159
                          · linarith only [h1, h159, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h150, h159, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h125, h156, h4, hc12, hc23, hlam, hphi]
                · linarith only [h150, h151, hc35, hlam, hphi, u3ehi3]
              · linarith only [h125, h150, h4, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h165 | h165
            · rcases m.htr 0 3 4 (by decide) (by decide) with h166 | h166
              · rcases m.htr 0 3 5 (by decide) (by decide) with h167 | h167
                · rcases m.htr 0 4 5 (by decide) (by decide) with h168 | h168
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h169 | h169
                    · linarith only [h0, h169, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                      · linarith only [h0, h125, h171, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                          · linarith only [h1, h174, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h166, h174, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h125, h165, h173, hc12, hc24, hlam, hphi]
                  · linarith only [h125, h165, h168, hlam]
                · linarith only [h166, h167, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h180 | h180
                · linarith only [h166, h180, hc34, hlam, hphi, u3ehi4]
                · linarith only [h165, h180, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h183 | h183
              · rcases m.htr 0 3 5 (by decide) (by decide) with h184 | h184
                · rcases m.htr 0 4 5 (by decide) (by decide) with h185 | h185
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h186 | h186
                    · linarith only [h0, h186, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
                      · linarith only [h0, h125, h188, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                        · linarith only [h0, h165, h190, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                          · linarith only [h1, h192, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h183, h192, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                    · linarith only [h0, h195, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h197 | h197
                      · linarith only [h0, h125, h197, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h199 | h199
                        · linarith only [h0, h165, h199, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h201 | h201
                          · linarith only [h1, h201, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                          · linarith only [h1, h183, h201, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                · linarith only [h183, h184, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h205 | h205
                · linarith only [h183, h205, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h207 | h207
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h208 | h208
                    · linarith only [h0, h208, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h210 | h210
                      · linarith only [h0, h125, h210, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h212 | h212
                        · linarith only [h0, h165, h212, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h214 | h214
                          · linarith only [h1, h183, h214, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h216 | h216
                            · linarith only [h1, h205, h216, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h218 | h218
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h219 | h219
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h220 | h220
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h221 | h221
                                    · rcases h0bigk with h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c | h222c
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [hlam, p222_0]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        rcases p222_3 (m.d 0 1) (by simp) with h224 | h224
                                        · rcases p222_3 (m.d 0 2) (by simp) with h225 | h225
                                          · linarith only [h0, h225, hlam]
                                          · rcases p222_3 (m.d 0 3) (by simp) with h227 | h227
                                            · linarith only [h1, h227, hlam]
                                            · linarith only [h227, h4, hlam]
                                        · linarith only [h0, h224, hlam]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p222_1, u0elo0, u3ehi1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h1, h205, h207, hlam, hphi, ht0b, ht34, ht45, ht5b, p222_1, u0elo0, u3ehi1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h1, h205, hlam, hphi, ht0b, ht34, ht45, ht5b, p222_1, u0elo0, u3ehi1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h0, hlam, p222_0]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [hlam, p222_0]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h4, hlam, p222_0]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h125, hlam, p222_1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h165, hlam, p222_0]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h1, hlam, p222_1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h0, h205, h219, h221, hc12, hc23, hlam, hphi, p222_1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [hlam, p222_0]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h183, hlam, p222_1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h205, hlam, p222_1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h2, hlam, p222_0]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h0, h183, h219, hc12, hc23, hlam, hphi, p222_1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h1, h183, h219, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p222_1, u3ehi1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [hlam, p222_0]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h1, h183, h205, h219, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p222_1, u3ehi1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h3, hlam, p222_0]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h0, h183, h207, h219, hc12, hc23, hlam, hphi, p222_1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h1, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, p222_1, u0elo0, u3ehi1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [h207, hlam, p222_1]
                                      · have p222_0 := h222c.1
                                        have p222_1 := h222c.2.1
                                        have p222_2 := h222c.2.2.1
                                        have p222_3 := h222c.2.2.2
                                        linarith only [hlam, p222_0]
                                    · linarith only [h183, h2, h218, h221, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h1, h183, h219, h220, hc35, hlam, hphi, u3ehi1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h256 | h256
                                  · linarith only [h219, h256, hc34, hlam, hphi, u3ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h258 | h258
                                    · rcases h0bigk with h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c | h259c
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [hlam, p259_0]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        rcases p259_3 (m.d 0 1) (by simp) with h261 | h261
                                        · rcases p259_3 (m.d 0 2) (by simp) with h262 | h262
                                          · linarith only [h0, h262, hlam]
                                          · rcases p259_3 (m.d 0 3) (by simp) with h264 | h264
                                            · linarith only [h1, h264, hlam]
                                            · linarith only [h264, h4, hlam]
                                        · linarith only [h0, h261, hlam]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1, u0elo0, u3ehi1]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h2, h218, hc45, hlam, hphi, ht0b, ht5b, p259_1, u0elo0]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h1, h205, hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1, u0elo0, u3ehi1]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h0, hlam, p259_0]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [hlam, p259_0]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h4, hlam, p259_0]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h125, hlam, p259_1]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h165, hlam, p259_0]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h1, hlam, p259_1]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h0, h256, h258, h4, hc12, hc34, hlam, hphi, ht23, p259_1]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [hlam, p259_0]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h183, hlam, p259_1]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h205, hlam, p259_1]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h2, hlam, p259_0]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        rcases p259_3 (m.d 0 1) (by simp) with h282 | h282
                                        · rcases p259_3 (m.d 0 2) (by simp) with h283 | h283
                                          · linarith only [h125, h283, hlam]
                                          · rcases p259_3 (m.d 0 3) (by simp) with h285 | h285
                                            · linarith only [h183, h285, hlam]
                                            · linarith only [h285, h4, hlam]
                                        · linarith only [h0, h282, hlam]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1, u0elo3, u3ehi1]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [hlam, p259_0]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h1, h2, h205, hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1, u0elo0, u3ehi1]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h3, hlam, p259_0]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        rcases p259_3 (m.d 0 1) (by simp) with h293 | h293
                                        · rcases p259_3 (m.d 0 2) (by simp) with h294 | h294
                                          · linarith only [h165, h294, hlam]
                                          · rcases p259_3 (m.d 0 3) (by simp) with h296 | h296
                                            · linarith only [h205, h296, hlam]
                                            · linarith only [h296, h4, hlam]
                                        · linarith only [h0, h293, hlam]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, p259_1, u0elo4, u3ehi1]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [h207, hlam, p259_1]
                                      · have p259_0 := h259c.1
                                        have p259_1 := h259c.2.1
                                        have p259_2 := h259c.2.2.1
                                        have p259_3 := h259c.2.2.2
                                        linarith only [hlam, p259_0]
                                    · linarith only [h1, h183, h258, hc45, hlam, hphi, ht34, u3ehi1]
                              · linarith only [h2, h207, h214, h218, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h305 | h305
                    · linarith only [h0, h305, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h307 | h307
                      · linarith only [h0, h125, h307, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h309 | h309
                        · linarith only [h0, h165, h309, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h311 | h311
                          · linarith only [h1, h183, h311, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h313 | h313
                            · linarith only [h1, h205, h313, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h315 | h315
                              · linarith only [h1, h183, h2, h207, h315, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h317 | h317
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h318 | h318
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h319 | h319
                                    · linarith only [h1, h183, h207, h317, h319, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                    · linarith only [h1, h183, h319, hc45, hlam, hphi, ht34, u3ehi1]
                                  · linarith only [h1, h183, h317, h318, hc35, hlam, hphi, u3ehi1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h323 | h323
                                  · linarith only [h317, h323, hc34, hlam, hphi, u3ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h325 | h325
                                    · linarith only [h1, h183, h207, h325, hc34, hlam, hphi, u3ehi1]
                                    · linarith only [h317, h325, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h328 | h328
        · rcases m.htr 0 2 4 (by decide) (by decide) with h329 | h329
          · rcases m.htr 0 2 5 (by decide) (by decide) with h330 | h330
            · linarith only [h0, h3, h330, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h332 | h332
              · rcases m.htr 0 3 5 (by decide) (by decide) with h333 | h333
                · linarith only [h0, h3, h328, h333, hlam]
                · linarith only [h332, h333, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h336 | h336
                · linarith only [h332, h336, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h338 | h338
                  · linarith only [h0, h3, h329, h338, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h340 | h340
                    · linarith only [h0, h340, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h328, h330, h340, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h343 | h343
            · linarith only [h0, h3, h343, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h345 | h345
              · linarith only [h328, h329, h345, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h347 | h347
                · linarith only [h345, h347, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h349 | h349
                  · linarith only [h2, h3, h349, hlam]
                  · linarith only [h328, h329, h349, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h352 | h352
          · rcases m.htr 0 2 5 (by decide) (by decide) with h353 | h353
            · linarith only [h0, h3, h353, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h355 | h355
              · rcases m.htr 0 3 5 (by decide) (by decide) with h356 | h356
                · linarith only [h1, h3, h356, hlam]
                · linarith only [h355, h356, hc35, hlam, hphi, u3ehi3]
              · linarith only [h328, h352, h355, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h360 | h360
            · linarith only [h1, h3, h328, h360, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h362 | h362
              · rcases m.htr 0 3 5 (by decide) (by decide) with h363 | h363
                · linarith only [h1, h3, h363, hlam]
                · linarith only [h362, h363, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h366 | h366
                · linarith only [h362, h366, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h368 | h368
                  · linarith only [h2, h3, h368, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
                    · linarith only [h0, h328, h370, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h372 | h372
                      · linarith only [h0, h3, h352, h362, h372, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h374 | h374
                        · linarith only [h0, h3, h360, h374, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h376 | h376
                          · linarith only [h1, h362, h376, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h378 | h378
                            · linarith only [h2, h3, h366, h376, h378, hlam]
                            · linarith only [h2, h3, h376, h378, hc35, hlam, hphi, u3ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h381 | h381
      · rcases m.htr 0 2 3 (by decide) (by decide) with h382 | h382
        · rcases m.htr 0 2 4 (by decide) (by decide) with h383 | h383
          · linarith only [h0, h2, h383, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h385 | h385
            · rcases m.htr 0 3 4 (by decide) (by decide) with h386 | h386
              · linarith only [h0, h2, h382, h386, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h388 | h388
                · linarith only [h386, h388, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h390 | h390
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h391 | h391
                    · linarith only [h0, h391, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h382, h383, h391, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2, h382, h390, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h395 | h395
              · linarith only [h2, h381, h382, h385, h395, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h397 | h397
                · linarith only [h395, h397, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h399 | h399
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h400 | h400
                    · linarith only [h0, h2, h400, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                    · linarith only [h382, h383, h400, hc12, hc24, hlam, hphi]
                  · linarith only [h2, h381, h382, h385, h399, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h404 | h404
          · linarith only [h0, h2, h404, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h406 | h406
            · rcases m.htr 0 3 4 (by decide) (by decide) with h407 | h407
              · linarith only [h1, h2, h407, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h409 | h409
                · linarith only [h407, h409, hc34, hlam, hphi, u3ehi4]
                · linarith only [h382, h406, h409, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h412 | h412
              · linarith only [h1, h2, h412, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h414 | h414
                · linarith only [h412, h414, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h416 | h416
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
                    · linarith only [h0, h417, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h419 | h419
                      · linarith only [h1, h2, h404, h417, h419, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h421 | h421
                        · linarith only [h0, h406, h421, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h423 | h423
                          · linarith only [h1, h2, h412, h419, h423, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h1, h2, h423, hc34, hlam, hphi, u3ehi1]
                  · linarith only [h1, h2, h416, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h427 | h427
        · rcases m.htr 0 2 4 (by decide) (by decide) with h428 | h428
          · linarith only [h0, h2, h428, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h430 | h430
            · linarith only [h0, h381, h430, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h432 | h432
              · linarith only [h0, h2, h427, h432, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h434 | h434
                · linarith only [h432, h434, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h436 | h436
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
                    · linarith only [h0, h437, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · linarith only [h427, h428, h437, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2, h427, h436, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h441 | h441
          · linarith only [h1, h2, h427, h441, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h443 | h443
            · linarith only [h1, h381, h427, h443, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h445 | h445
              · linarith only [h1, h2, h445, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h447 | h447
                · linarith only [h445, h447, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h449 | h449
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
                    · linarith only [h0, h381, h427, h449, h450, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h452 | h452
                      · linarith only [h0, h381, h441, h449, h452, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h454 | h454
                        · linarith only [h1, h443, h450, h454, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h456 | h456
                          · linarith only [h1, h2, h445, h452, h456, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h1, h2, h456, hc34, hlam, hphi, u3ehi1]
                  · linarith only [h1, h2, h449, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h460 | h460
    · rcases m.htr 0 1 5 (by decide) (by decide) with h461 | h461
      · rcases m.htr 0 2 3 (by decide) (by decide) with h462 | h462
        · linarith only [h0, h1, h462, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h464 | h464
          · rcases m.htr 0 2 5 (by decide) (by decide) with h465 | h465
            · rcases m.htr 0 3 4 (by decide) (by decide) with h466 | h466
              · rcases m.htr 0 3 5 (by decide) (by decide) with h467 | h467
                · rcases m.htr 0 4 5 (by decide) (by decide) with h468 | h468
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h469 | h469
                    · linarith only [h0, h462, h469, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h471 | h471
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h472 | h472
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h473 | h473
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h474 | h474
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h475 | h475
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h476 | h476
                                · linarith only [h0, h1, h469, h471, h476, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h1, h469, h476, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h464, h468, h473, h475, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                            · linarith only [h0, h1, h474, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h464, h466, h473, hlam]
                        · linarith only [h0, h465, h471, h472, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h464, h469, h471, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h484 | h484
                    · linarith only [h0, h1, h484, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h486 | h486
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h487 | h487
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h489 | h489
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h490 | h490
                              · linarith only [h460, h468, h490, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
                                · linarith only [h0, h1, h484, h486, h492, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h1, h460, h484, h488, h492, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h0, h1, h467, h486, h488, h489, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                          · linarith only [h0, h1, h488, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h465, h486, h487, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1, h464, h484, h486, hc12, hc23, hlam, hphi]
                · linarith only [h466, h467, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h460, h466, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h501 | h501
              · rcases m.htr 0 3 5 (by decide) (by decide) with h502 | h502
                · rcases m.htr 0 4 5 (by decide) (by decide) with h503 | h503
                  · linarith only [h464, h465, h503, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h505 | h505
                    · linarith only [h0, h505, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h507 | h507
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h508 | h508
                        · linarith only [h0, h1, h465, h505, h508, hc02, hc23, hlam, hphi]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h510 | h510
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h511 | h511
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h512 | h512
                              · linarith only [h460, h503, h512, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                                · linarith only [h0, h1, h505, h507, h514, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h1, h460, h461, h505, h508, h510, h514, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h1, h461, h507, h508, h510, h511, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h1, h461, h508, h510, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h464, h465, h507, hc12, hc25, hlam, hphi]
                · linarith only [h501, h502, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h460, h501, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h522 | h522
            · rcases m.htr 0 3 4 (by decide) (by decide) with h523 | h523
              · rcases m.htr 0 3 5 (by decide) (by decide) with h524 | h524
                · rcases m.htr 0 4 5 (by decide) (by decide) with h525 | h525
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h526 | h526
                    · linarith only [h0, h526, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h528 | h528
                      · linarith only [h0, h1, h464, h526, h528, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h530 | h530
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h531 | h531
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h532 | h532
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h533 | h533
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h534 | h534
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h535 | h535
                                  · linarith only [h1, h460, h526, h528, h530, h535, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                                  · linarith only [h1, h460, h461, h526, h528, h532, h535, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                                · linarith only [h1, h460, h526, h528, h530, h532, h534, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h525, h528, h530, h532, h533, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                            · linarith only [h1, h460, h528, h532, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h460, h528, h530, h531, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h460, h464, h522, h526, h530, hc12, hc23, hlam, hphi]
                  · linarith only [h464, h522, h525, hlam]
                · linarith only [h523, h524, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h460, h523, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h546 | h546
              · rcases m.htr 0 3 5 (by decide) (by decide) with h547 | h547
                · rcases m.htr 0 4 5 (by decide) (by decide) with h548 | h548
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h549 | h549
                    · linarith only [h0, h549, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h551 | h551
                      · linarith only [h0, h1, h464, h549, h551, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h553 | h553
                        · linarith only [h0, h522, h553, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h555 | h555
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h556 | h556
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h557 | h557
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h558 | h558
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h559 | h559
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h560 | h560
                                    · rcases h0bigk with h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h1, h549, hc02, hc23, hlam, hphi, p561_1]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h1, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h0, h1, h464, h549, hc12, hc23, hlam, hphi, p561_1]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h0, h1, h522, h549, hc12, hc23, hlam, hphi, p561_1]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h0, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h462, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h464, hlam, p561_1]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h522, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p561_1, u0elo2]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        rcases p561_3 (m.d 0 1) (by simp) with h573 | h573
                                        · linarith only [h1, h573, hlam]
                                        · linarith only [h0, h573, hlam]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h460, h555, h560, hlam, hphi, ht0b, ht34, ht45, ht5b, p561_1, u0elo2, u3ehi4]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h461, h556, hlam, hphi, ht0b, ht34, ht45, ht5b, p561_1, u0elo2, u3ehi4]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h460, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h0, h1, h460, h549, hc12, hc23, hlam, hphi, p561_1]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h546, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h1, h460, h461, h549, h556, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p561_1, u3ehi4]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h461, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h0, h1, h461, h549, hc12, hc23, hlam, hphi, p561_1]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h547, hlam, p561_0]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [h548, hlam, p561_1]
                                      · have p561_0 := h561c.1
                                        have p561_1 := h561c.2.1
                                        have p561_2 := h561c.2.2.1
                                        have p561_3 := h561c.2.2.2
                                        linarith only [hlam, p561_0]
                                    · linarith only [h1, h460, h548, h549, h560, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h1, h460, h549, h557, h559, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1, h460, h549, h556, h557, h558, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h460, h548, h555, h557, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                            · linarith only [h0, h1, h556, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h555, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h595 | h595
                    · linarith only [h0, h595, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h597 | h597
                      · linarith only [h0, h1, h464, h595, h597, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h599 | h599
                        · linarith only [h0, h522, h599, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h601 | h601
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h602 | h602
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h603 | h603
                              · linarith only [h1, h460, h548, h595, h603, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h605 | h605
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h606 | h606
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h607 | h607
                                    · linarith only [h1, h460, h461, h548, h595, h601, h602, h607, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                                    · rcases h0bigk with h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c | h609c
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h1, h595, hc02, hc23, hlam, hphi, p609_1]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h1, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h0, h1, h464, h595, hc12, hc23, hlam, hphi, p609_1]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h0, h1, h522, h595, hc12, hc23, hlam, hphi, p609_1]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h0, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h462, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h464, hlam, p609_1]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h522, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p609_1, u0elo2]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        rcases p609_3 (m.d 0 1) (by simp) with h621 | h621
                                        · linarith only [h1, h621, hlam]
                                        · linarith only [h0, h621, hlam]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h460, h601, hlam, hphi, ht0b, ht34, ht45, ht5b, p609_1, u0elo2, u3ehi3]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h460, h548, h601, hlam, hphi, ht0b, ht34, ht45, ht5b, p609_1, u0elo2, u3ehi3]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h460, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h0, h1, h461, h548, h595, h602, h607, hc12, hc23, hc45, hlam, hphi, ht34, p609_1, u3ehi3]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h546, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h548, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h461, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h0, h1, h461, h595, hc12, hc23, hlam, hphi, p609_1]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h547, hlam, p609_0]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [h1, h460, h461, h595, h601, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p609_1, u3ehi3]
                                      · have p609_0 := h609c.1
                                        have p609_1 := h609c.2.1
                                        have p609_2 := h609c.2.2.1
                                        have p609_3 := h609c.2.2.2
                                        linarith only [hlam, p609_0]
                                  · linarith only [h0, h1, h595, h606, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h1, h461, h595, h601, h603, h605, hlam]
                            · linarith only [h0, h1, h602, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h461, h546, h548, h601, hlam]
                · linarith only [h546, h547, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h460, h546, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h643 | h643
        · linarith only [h0, h1, h643, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h645 | h645
          · rcases m.htr 0 2 5 (by decide) (by decide) with h646 | h646
            · linarith only [h0, h461, h646, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h648 | h648
              · rcases m.htr 0 3 5 (by decide) (by decide) with h649 | h649
                · rcases m.htr 0 4 5 (by decide) (by decide) with h650 | h650
                  · linarith only [h0, h461, h645, h650, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h652 | h652
                    · linarith only [h0, h643, h652, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h654 | h654
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h655 | h655
                        · linarith only [h0, h461, h646, h655, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h657 | h657
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h658 | h658
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h659 | h659
                              · linarith only [h460, h650, h659, hlam]
                              · linarith only [h0, h461, h654, h657, h659, hc45, hlam, hphi, ht34, u3ehi3]
                            · linarith only [h649, h658, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · linarith only [h0, h1, h657, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h643, h645, h654, hc12, hc23, hlam, hphi]
                · linarith only [h648, h649, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h460, h648, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h667 | h667
            · linarith only [h0, h461, h667, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h669 | h669
              · rcases m.htr 0 3 5 (by decide) (by decide) with h670 | h670
                · rcases m.htr 0 4 5 (by decide) (by decide) with h671 | h671
                  · linarith only [h460, h461, h671, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h673 | h673
                    · linarith only [h0, h643, h673, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h675 | h675
                      · linarith only [h0, h645, h675, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h677 | h677
                        · linarith only [h0, h461, h667, h677, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h679 | h679
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h680 | h680
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h681 | h681
                              · linarith only [h460, h461, h645, h671, h673, h680, h681, hc02, hc23, hlam, hphi]
                              · linarith only [h460, h461, h679, h681, hc45, hlam, hphi, ht34, u3ehi3]
                            · linarith only [h670, h680, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · linarith only [h0, h1, h679, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h669, h670, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1, h460, h669, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h688 | h688
      · rcases m.htr 0 2 3 (by decide) (by decide) with h689 | h689
        · linarith only [h0, h1, h689, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h691 | h691
          · linarith only [h0, h460, h691, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h693 | h693
            · rcases m.htr 0 3 4 (by decide) (by decide) with h694 | h694
              · rcases m.htr 0 3 5 (by decide) (by decide) with h695 | h695
                · rcases m.htr 0 4 5 (by decide) (by decide) with h696 | h696
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h697 | h697
                    · linarith only [h0, h689, h697, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h699 | h699
                      · linarith only [h0, h460, h691, h699, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h701 | h701
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h702 | h702
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h703 | h703
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h704 | h704
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h705 | h705
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h706 | h706
                                  · linarith only [h0, h701, h706, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                                  · linarith only [h0, h460, h697, h702, h706, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h460, h694, h697, h701, h702, h703, h705, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
                              · linarith only [h0, h460, h701, h703, h704, hc45, hlam, hphi, ht34, u3ehi4]
                            · linarith only [h0, h460, h701, h702, h703, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h694, h702, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                        · linarith only [h0, h1, h693, h697, h701, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h460, h693, h696, hlam]
                · linarith only [h694, h695, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h716 | h716
                · linarith only [h694, h716, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h1, h693, h716, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h719 | h719
              · rcases m.htr 0 3 5 (by decide) (by decide) with h720 | h720
                · rcases m.htr 0 4 5 (by decide) (by decide) with h721 | h721
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h722 | h722
                    · linarith only [h0, h689, h722, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h724 | h724
                      · linarith only [h0, h691, h724, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h726 | h726
                        · linarith only [h0, h693, h726, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h728 | h728
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h729 | h729
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h730 | h730
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h731 | h731
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h732 | h732
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h733 | h733
                                    · rcases h0bigk with h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [hlam, p734_0]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h460, h722, h728, hc02, hc23, hlam, hphi, p734_1]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h1, hlam, p734_0]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h460, hlam, p734_1]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h460, h688, h722, h728, h729, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p734_1, u3ehi4]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h0, hlam, p734_0]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [hlam, p734_0]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h689, hlam, p734_0]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h691, hlam, p734_1]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h693, hlam, p734_0]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p734_1, u0elo2]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        rcases p734_3 (m.d 0 1) (by simp) with h746 | h746
                                        · linarith only [h1, h746, hlam]
                                        · linarith only [h0, h746, hlam]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [hlam, p734_0]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h460, h688, h729, hlam, hphi, ht0b, ht34, ht45, ht5b, p734_1, u0elo2, u3ehi4]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h688, h729, hlam, hphi, ht0b, ht34, ht45, ht5b, p734_1, u0elo2, u3ehi4]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h688, h729, hlam, hphi, ht0b, ht34, ht45, ht5b, p734_1, u0elo3, u3ehi4]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        rcases p734_3 (m.d 0 1) (by simp) with h753 | h753
                                        · linarith only [h460, h753, hlam]
                                        · linarith only [h0, h753, hlam]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h719, hlam, p734_0]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [hlam, p734_0]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h688, h719, h729, hlam, hphi, ht0b, ht34, ht45, ht5b, p734_1, u0elo2, u3ehi4]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h688, hlam, p734_0]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h0, h460, h688, h722, h728, hc12, hc23, hlam, hphi, p734_1]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h720, hlam, p734_0]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [h721, hlam, p734_1]
                                      · have p734_0 := h734c.1
                                        have p734_1 := h734c.2.1
                                        have p734_2 := h734c.2.2.1
                                        have p734_3 := h734c.2.2.2
                                        linarith only [hlam, p734_0]
                                    · linarith only [h719, h721, h733, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                  · linarith only [h460, h688, h722, h728, h729, h732, hlam]
                                · linarith only [h460, h688, h722, h728, h729, h731, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h460, h688, h729, h730, hc45, hlam, hphi, ht34, u3ehi4]
                            · linarith only [h0, h460, h728, h729, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h719, h728, hlam]
                  · linarith only [h460, h688, h721, hlam]
                · linarith only [h719, h720, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h772 | h772
                · linarith only [h719, h772, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1, h688, h772, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h775 | h775
        · linarith only [h0, h1, h775, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h777 | h777
          · linarith only [h0, h460, h777, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h779 | h779
            · linarith only [h0, h688, h779, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h781 | h781
              · rcases m.htr 0 3 5 (by decide) (by decide) with h782 | h782
                · rcases m.htr 0 4 5 (by decide) (by decide) with h783 | h783
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h784 | h784
                    · linarith only [h0, h688, h775, h781, h783, h784, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h786 | h786
                      · linarith only [h0, h688, h777, h783, h786, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h788 | h788
                        · linarith only [h0, h779, h788, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h790 | h790
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h791 | h791
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h792 | h792
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h793 | h793
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h794 | h794
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h795 | h795
                                    · rcases h0bigk with h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c | h796c
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [hlam, p796_0]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h0, h688, h784, h790, h792, hc12, hc23, hlam, hphi, p796_1]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h1, hlam, p796_0]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h460, hlam, p796_1]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h688, hlam, p796_1]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h0, hlam, p796_0]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [hlam, p796_0]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h775, hlam, p796_0]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h777, hlam, p796_1]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h779, hlam, p796_0]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p796_1, u0elo2]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        rcases p796_3 (m.d 0 1) (by simp) with h808 | h808
                                        · linarith only [h1, h808, hlam]
                                        · linarith only [h0, h808, hlam]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [hlam, p796_0]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h0, h460, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p796_1, u0elo2]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h0, h688, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p796_1, u0elo2]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p796_1, u0elo3]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        rcases p796_3 (m.d 0 1) (by simp) with h815 | h815
                                        · linarith only [h460, h815, hlam]
                                        · linarith only [h0, h815, hlam]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h781, hlam, p796_0]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [hlam, p796_0]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h781, h782, hlam, hphi, ht0b, ht34, ht45, ht5b, p796_1, u0elo2, u3ehi4]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p796_1, u0elo4]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        rcases p796_3 (m.d 0 1) (by simp) with h822 | h822
                                        · linarith only [h688, h822, hlam]
                                        · linarith only [h0, h822, hlam]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h782, hlam, p796_0]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [h783, hlam, p796_1]
                                      · have p796_0 := h796c.1
                                        have p796_1 := h796c.2.1
                                        have p796_2 := h796c.2.2.1
                                        have p796_3 := h796c.2.2.2
                                        linarith only [hlam, p796_0]
                                    · linarith only [h781, h783, h795, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                                  · linarith only [h0, h1, h784, h794, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h1, h782, h784, h793, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h460, h783, h792, hlam]
                            · linarith only [h1, h782, h791, hlam]
                          · linarith only [h1, h781, h790, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h834 | h834
                    · linarith only [h0, h834, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h836 | h836
                      · linarith only [h0, h460, h783, h836, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h838 | h838
                        · linarith only [h0, h460, h779, h783, h838, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h842 | h842
                              · linarith only [h0, h460, h783, h834, h840, h842, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h460, h842, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h782, h841, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                          · linarith only [h0, h1, h840, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h781, h782, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h848 | h848
                · linarith only [h781, h848, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h850 | h850
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h851 | h851
                    · linarith only [h0, h851, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h853 | h853
                      · linarith only [h0, h777, h853, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h855 | h855
                        · linarith only [h0, h779, h855, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h857 | h857
                          · linarith only [h0, h1, h781, h851, h857, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h857, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h860 | h860
                    · linarith only [h0, h860, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h862 | h862
                      · linarith only [h0, h460, h850, h862, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h864 | h864
                        · linarith only [h0, h779, h864, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h866 | h866
                          · linarith only [h0, h1, h781, h860, h866, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h866, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 4696000 in
set_option maxHeartbeats 4696000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h869 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h870 | h870
  · rcases m.htr 0 1 5 (by decide) (by decide) with h871 | h871
    · rcases m.htr 0 2 3 (by decide) (by decide) with h872 | h872
      · rcases m.htr 0 2 4 (by decide) (by decide) with h873 | h873
        · rcases m.htr 0 2 5 (by decide) (by decide) with h874 | h874
          · rcases m.htr 0 3 4 (by decide) (by decide) with h875 | h875
            · rcases m.htr 0 3 5 (by decide) (by decide) with h876 | h876
              · rcases m.htr 0 4 5 (by decide) (by decide) with h877 | h877
                · rcases m.htr 1 2 3 (by decide) (by decide) with h878 | h878
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h879 | h879
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h880 | h880
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h881 | h881
                        · linarith only [h869, h881, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h875, h881, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h869, h875, h880, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h869, h875, h879, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h869, h875, h878, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h887 | h887
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h888 | h888
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h889 | h889
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h890 | h890
                        · linarith only [h869, h890, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h875, h890, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h869, h875, h889, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h869, h875, h888, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h869, h875, h887, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h875, h876, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h897 | h897
              · linarith only [h875, h897, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h899 | h899
                · rcases m.htr 1 2 3 (by decide) (by decide) with h900 | h900
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h901 | h901
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h902 | h902
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h903 | h903
                        · linarith only [h869, h875, h903, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h905 | h905
                          · linarith only [h0, h869, h905, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h907 | h907
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h908 | h908
                              · linarith only [h869, h897, h900, h908, hc35, hlam, hphi, u3ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h910 | h910
                                · linarith only [h0, h870, h897, h900, h905, h907, h910, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h912 | h912
                                  · rcases h0bigk with h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [hlam, p913_0]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h0, hlam, p913_1]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h0, h869, h900, hlam, hphi, ht0b, ht34, ht45, ht5b, p913_1, u0elo1, u3ehi2]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h0, h870, h907, hc45, hlam, hphi, ht0b, ht5b, p913_1, u0elo1]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h0, h869, h897, h900, hlam, hphi, ht0b, ht34, ht45, ht5b, p913_1, u0elo1, u3ehi2]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h869, h900, hlam, hphi, ht0b, ht34, ht45, ht5b, p913_1, u0elo1, u3ehi2]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [hlam, p913_0]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h869, h900, hlam, hphi, ht0b, ht34, ht45, ht5b, p913_1, u0elo1, u3ehi2]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h869, h875, h900, hlam, hphi, ht0b, ht34, ht45, ht5b, p913_1, u0elo1, u3ehi2]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h869, h897, h900, hlam, hphi, ht0b, ht34, ht45, ht5b, p913_1, u0elo1, u3ehi2]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h869, hlam, p913_1]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h872, hlam, p913_1]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [hlam, p913_0]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h875, hlam, p913_1]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h897, hlam, p913_1]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h870, hlam, p913_0]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h873, hlam, p913_0]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h869, h900, hlam, hphi, ht0b, ht34, ht45, ht5b, p913_1, u0elo3, u3ehi2]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [hlam, p913_0]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h869, h870, h897, h900, hlam, hphi, ht0b, ht34, ht45, ht5b, p913_1, u0elo0, u3ehi2]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h871, hlam, p913_0]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h874, hlam, p913_1]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h869, h900, hlam, hphi, ht0b, ht34, ht45, ht5b, p913_1, u0elo4, u3ehi2]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [h899, hlam, p913_1]
                                    · have p913_0 := h913c.1
                                      have p913_1 := h913c.2.1
                                      have p913_2 := h913c.2.2.1
                                      have p913_3 := h913c.2.2.2
                                      linarith only [hlam, p913_0]
                                  · linarith only [h869, h875, h900, h912, hc45, hlam, hphi, ht34, u3ehi2]
                            · linarith only [h899, h900, h903, h907, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                      · linarith only [h0, h869, h900, h902, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h869, h900, h901, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h869, h900, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h944 | h944
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h945 | h945
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h946 | h946
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h947 | h947
                        · linarith only [h869, h947, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h949 | h949
                          · linarith only [h869, h897, h949, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h951 | h951
                            · linarith only [h0, h870, h899, h951, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h953 | h953
                              · linarith only [h872, h875, h953, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h955 | h955
                                · linarith only [h869, h897, h944, h955, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h957 | h957
                                  · linarith only [h869, h875, h899, h944, h957, hc34, hlam, hphi, u3ehi2]
                                  · linarith only [h869, h875, h944, h957, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h869, h944, h946, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h869, h873, h944, h945, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                  · linarith only [h0, h869, h944, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h871, h874, hlam]
        · linarith only [h0, h870, h873, hlam]
      · linarith only [h0, h869, h872, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h966 | h966
      · rcases m.htr 0 2 4 (by decide) (by decide) with h967 | h967
        · rcases m.htr 0 2 5 (by decide) (by decide) with h968 | h968
          · rcases m.htr 0 3 4 (by decide) (by decide) with h969 | h969
            · rcases m.htr 0 3 5 (by decide) (by decide) with h970 | h970
              · linarith only [h869, h871, h970, hlam]
              · linarith only [h969, h970, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h973 | h973
              · linarith only [h969, h973, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h975 | h975
                · linarith only [h870, h871, h975, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h977 | h977
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h978 | h978
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h979 | h979
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h980 | h980
                        · linarith only [h869, h871, h968, h969, h980, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h982 | h982
                          · linarith only [h869, h969, h982, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h870, h871, h977, h980, h982, hc35, hlam, hphi, u3ehi2]
                      · linarith only [h0, h968, h979, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h869, h977, h978, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h869, h977, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h988 | h988
            · rcases m.htr 0 3 5 (by decide) (by decide) with h989 | h989
              · linarith only [h869, h871, h989, hlam]
              · linarith only [h988, h989, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h992 | h992
              · linarith only [h988, h992, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h994 | h994
                · linarith only [h0, h870, h968, h994, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h996 | h996
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h997 | h997
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h998 | h998
                      · linarith only [h0, h869, h968, h996, h998, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h869, h996, h998, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h869, h996, h997, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h869, h996, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h0, h870, h967, hlam]
      · linarith only [h0, h869, h966, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1005 | h1005
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1006 | h1006
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1007 | h1007
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1008 | h1008
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1009 | h1009
            · linarith only [h1009, h869, h870, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1011 | h1011
              · linarith only [h1009, h1011, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1013 | h1013
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1014 | h1014
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1015 | h1015
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1016 | h1016
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1017 | h1017
                        · linarith only [h1009, h1017, h869, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · linarith only [h1014, h1017, h869, h870, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1014, h1015, h1016, h869, h870, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1007, h1015, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1014, h869, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1013, h869, h870, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h1005, h1008, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1025 | h1025
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1026 | h1026
            · linarith only [h0, h1007, h1026, h869, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1028 | h1028
              · linarith only [h1026, h1028, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1030 | h1030
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1031 | h1031
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1032 | h1032
                    · linarith only [h0, h1007, h1032, h869, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h1031, h1032, h869, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1031, h869, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1030, h869, h870, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h1005, h1025, hlam]
      · linarith only [h0, h1006, h869, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1039 | h1039
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1040 | h1040
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1041 | h1041
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1042 | h1042
            · linarith only [h1042, h869, h870, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1044 | h1044
              · linarith only [h1042, h1044, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1046 | h1046
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1047 | h1047
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1048 | h1048
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1049 | h1049
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1050 | h1050
                        · linarith only [h1005, h1040, h1042, h1046, h1050, h869, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                        · linarith only [h1047, h1050, h869, h870, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1041, h1047, h1048, h1049, h869, h870, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                    · linarith only [h0, h1040, h1047, h1048, h869, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                  · linarith only [h0, h1047, h869, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1046, h869, h870, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1057 | h1057
            · linarith only [h1057, h869, h870, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1059 | h1059
              · linarith only [h1057, h1059, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1061 | h1061
                · linarith only [h1040, h1041, h1061, hlam]
                · linarith only [h1061, h869, h870, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1064 | h1064
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1065 | h1065
            · linarith only [h0, h1040, h1065, h869, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1067 | h1067
              · linarith only [h1065, h1067, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1069 | h1069
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1070 | h1070
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1071 | h1071
                    · linarith only [h1005, h1040, h1064, h1070, h1071, h869, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1070, h1071, h869, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1070, h869, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1005, h1040, h1064, h1069, h869, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1076 | h1076
            · linarith only [h0, h1040, h1076, h869, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1078 | h1078
              · linarith only [h1076, h1078, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1080 | h1080
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1081 | h1081
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1082 | h1082
                    · linarith only [h0, h1040, h1081, h1082, h869, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1081, h1082, h869, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1081, h869, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1080, h869, h870, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h0, h1039, h869, hlam]

set_option maxHeartbeats 4696000 in
set_option maxHeartbeats 4696000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h869 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1088 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1089 | h1089
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1090 | h1090
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1091 | h1091
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1092 | h1092
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1093 | h1093
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1094 | h1094
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1095 | h1095
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1096 | h1096
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1097 | h1097
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1098 | h1098
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1099 | h1099
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1100 | h1100
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1101 | h1101
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1102 | h1102
                            · linarith only [h1090, h1102, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · linarith only [h1093, h1102, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                          · linarith only [h1088, h1095, h1099, h1101, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h1088, h1099, h1100, h869, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1094, h1099, h869, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1088, h1092, h1094, h1095, h1096, h1098, h869, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                  · linarith only [h0, h1091, h1097, hlam]
                · linarith only [h0, h1090, h1096, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1111 | h1111
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1112 | h1112
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1113 | h1113
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1114 | h1114
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1115 | h1115
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1116 | h1116
                          · linarith only [h1088, h1095, h1116, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1118 | h1118
                            · linarith only [h1090, h1118, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · linarith only [h1089, h1114, h1116, h1118, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                        · linarith only [h1088, h1114, h1115, h869, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1093, h1095, h1114, h869, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h1089, h1092, h1093, h1095, h1111, h1113, h869, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                  · linarith only [h0, h1091, h1112, hlam]
                · linarith only [h0, h1090, h1111, hlam]
            · linarith only [h1093, h1094, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1088, h1093, h869, hlam]
        · linarith only [h0, h1089, h1092, hlam]
      · linarith only [h0, h1088, h1091, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1130 | h1130
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1131 | h1131
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1132 | h1132
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1133 | h1133
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1134 | h1134
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1135 | h1135
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1136 | h1136
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1137 | h1137
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1138 | h1138
                      · linarith only [h0, h1088, h1090, h1135, h1138, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h1090, h1132, h1135, h1138, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1088, h1090, h1133, h1134, h1135, h1137, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h0, h1088, h1090, h1133, h1134, h1135, h1136, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1143 | h1143
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1144 | h1144
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1145 | h1145
                      · linarith only [h0, h1088, h1135, h1145, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1088, h1133, h1134, h1145, h869, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h0, h1088, h1131, h1133, h1134, h1144, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                  · linarith only [h0, h1130, h1143, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1150 | h1150
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1151 | h1151
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1152 | h1152
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1153 | h1153
                      · linarith only [h0, h1088, h1090, h1150, h1153, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h1088, h1090, h1132, h1134, h1150, h1153, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h0, h1089, h1090, h1132, h1134, h1150, h1152, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1089, h1090, h1132, h1134, h1150, h1151, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1158 | h1158
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1159 | h1159
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1160 | h1160
                      · linarith only [h0, h1088, h1150, h1160, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1088, h1132, h1160, h869, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h1089, h1131, h1132, h1134, h1159, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                  · linarith only [h0, h1130, h1158, hlam]
            · linarith only [h1132, h1133, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1088, h1090, h1132, hlam]
        · linarith only [h0, h1089, h1131, hlam]
      · linarith only [h0, h1088, h1130, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1169 | h1169
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1170 | h1170
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1171 | h1171
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1172 | h1172
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1173 | h1173
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1174 | h1174
              · linarith only [h1088, h1089, h1174, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1176 | h1176
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1177 | h1177
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1178 | h1178
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1179 | h1179
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1180 | h1180
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1181 | h1181
                          · linarith only [h1088, h1174, h1181, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1088, h1089, h1179, h1181, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h1088, h1179, h1180, h869, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1173, h1179, h869, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h0, h1171, h1178, hlam]
                  · linarith only [h0, h1170, h1177, hlam]
                · linarith only [h0, h1169, h1176, hlam]
            · linarith only [h1172, h1173, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1088, h1172, h869, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1191 | h1191
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1192 | h1192
            · linarith only [h1169, h1171, h1192, hlam]
            · linarith only [h1191, h1192, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1088, h1191, h869, hlam]
      · linarith only [h0, h1088, h1170, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1197 | h1197
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1198 | h1198
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1199 | h1199
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1200 | h1200
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1201 | h1201
              · linarith only [h1088, h1089, h1201, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1203 | h1203
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1204 | h1204
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1205 | h1205
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1206 | h1206
                      · linarith only [h1088, h1089, h1169, h1198, h1203, h1206, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1089, h1169, h1198, h1199, h1203, h1206, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1169, h1198, h1203, h1205, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                  · linarith only [h1169, h1203, h1204, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1211 | h1211
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1212 | h1212
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1213 | h1213
                      · linarith only [h1088, h1089, h1203, h1212, h1213, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1089, h1199, h1203, h1212, h1213, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1088, h1198, h1199, h1212, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                  · linarith only [h0, h1197, h1211, hlam]
            · linarith only [h1199, h1200, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1088, h1169, h1199, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1220 | h1220
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1221 | h1221
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1222 | h1222
              · linarith only [h0, h1088, h1198, h1222, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1224 | h1224
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1225 | h1225
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1226 | h1226
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1227 | h1227
                      · linarith only [h0, h1088, h1169, h1224, h1227, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h1169, h1220, h1224, h1227, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1088, h1169, h1220, h1224, h1226, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1088, h1169, h1220, h1224, h1225, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1232 | h1232
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1233 | h1233
                    · linarith only [h0, h1088, h1198, h1220, h1224, h1233, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1235 | h1235
                      · linarith only [h0, h1088, h1224, h1235, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1220, h1222, h1235, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h0, h1197, h1232, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h1220, h1221, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1088, h1169, h1220, hlam]
      · linarith only [h0, h1088, h1197, hlam]

set_option maxHeartbeats 4696000 in
set_option maxHeartbeats 4696000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h869 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1088 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1242 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1243 | h1243
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1244 | h1244
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1245 | h1245
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1246 | h1246
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1247 | h1247
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1248 | h1248
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1249 | h1249
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1250 | h1250
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1251 | h1251
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1252 | h1252
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1253 | h1253
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1254 | h1254
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1255 | h1255
                          · linarith only [h1243, h1255, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                          · linarith only [h1246, h1255, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                        · linarith only [h1088, h1242, h1253, h1254, hc45, hlam, hphi, ht34, u3ehi4]
                      · linarith only [h1088, h1242, h1247, h1252, h1253, hlam]
                    · linarith only [h1242, h1247, h1252, h869, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h1245, h1251, hlam]
                · linarith only [h1242, h1244, h1247, h1249, h1250, h869, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
              · linarith only [h0, h1243, h1249, hlam]
            · linarith only [h1088, h1242, h1248, hlam]
          · linarith only [h1246, h1247, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1266 | h1266
          · linarith only [h1246, h1266, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1242, h1266, h869, hlam]
      · linarith only [h0, h1242, h1245, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1270 | h1270
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1271 | h1271
        · linarith only [h1243, h1244, h1271, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1273 | h1273
          · linarith only [h1271, h1273, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1242, h1273, h869, hlam]
      · linarith only [h0, h1242, h1270, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1277 | h1277
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1278 | h1278
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1279 | h1279
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1280 | h1280
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1281 | h1281
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1282 | h1282
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1283 | h1283
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1284 | h1284
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1285 | h1285
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1286 | h1286
                      · linarith only [h1088, h1242, h1243, h1277, h1282, h1286, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h1279, h1286, h869, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1243, h1277, h1279, h1282, h1285, hlam]
                  · linarith only [h1243, h1282, h1284, hc02, hc25, hlam, hphi]
                · linarith only [h1243, h1277, h1282, h1283, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1292 | h1292
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1293 | h1293
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1294 | h1294
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1295 | h1295
                      · linarith only [h1088, h1242, h1282, h1292, h1295, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h1279, h1295, h869, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1088, h1242, h1279, h1280, h1282, h1292, h1294, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
                  · linarith only [h1088, h1242, h1278, h1280, h1292, h1293, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                · linarith only [h0, h1277, h1292, hlam]
            · linarith only [h1088, h1242, h1281, hlam]
          · linarith only [h1279, h1280, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1243, h1277, h1279, hlam]
      · linarith only [h0, h1242, h1278, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1305 | h1305
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1306 | h1306
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1307 | h1307
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1308 | h1308
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1309 | h1309
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1310 | h1310
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1311 | h1311
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1312 | h1312
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1313 | h1313
                      · linarith only [h0, h1242, h1243, h1309, h1313, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h1306, h1313, h869, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1243, h1306, h1309, h1312, hlam]
                  · linarith only [h0, h1242, h1243, h1307, h1309, h1311, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h1243, h1309, h1310, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1319 | h1319
                · linarith only [h0, h1242, h1277, h1307, h1309, h1319, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1321 | h1321
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1322 | h1322
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1323 | h1323
                      · linarith only [h0, h1242, h1309, h1323, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h0, h1242, h1307, h1319, h1322, h1323, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                    · linarith only [h1306, h1322, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h0, h1242, h1305, h1307, h1321, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
            · linarith only [h0, h1242, h1277, h1308, hlam]
          · linarith only [h1306, h1307, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1330 | h1330
          · linarith only [h1306, h1330, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1242, h1330, h869, hlam]
      · linarith only [h0, h1242, h1305, hlam]

end R2N4
